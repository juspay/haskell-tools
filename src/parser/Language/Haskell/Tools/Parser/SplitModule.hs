
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}

module Language.Haskell.Tools.Parser.SplitModule where

import Language.Haskell.Tools.Refactor as Refactor hiding (LambdaCase)
import Language.Haskell.Tools.Refactor.Utils.Extensions
import Language.Haskell.Tools.Rewrite.Match.Binds
import Control.Monad.Reader
import Control.Monad.State
import Control.Concurrent.MVar
import GHC hiding (Name, mkModuleName, mkMatch)
import Module as GHC hiding (mkModuleName)
import InstEnv as GHC
import Unify as GHC
import Type as GHC
import Var as GHC
import UniqSupply as GHC
import Unique as GHC
import TysWiredIn as GHC
import TysPrim as GHC
import PrelNames as GHC
import ConLike as GHC
import PatSyn as GHC
import BasicTypes as GHC

import Control.Reference
import Data.Char (isAlphaNum)
import Data.Function (on)
import Data.Maybe (mapMaybe)
import Data.List
import Data.Foldable
import qualified Data.Map.Strict as SMap (empty, toList)

import Debug.Trace (trace, traceShowId)
import Language.Haskell.Tools.Debug.RangeDebug
import Language.Haskell.Tools.Debug.RangeDebugInstances
import Outputable hiding ((<>))
import Language.Haskell.Tools.PrettyPrint

import Language.Haskell.Tools.BackendGHC.Exprs (trfExpr)
import Language.Haskell.Tools.BackendGHC.GHCUtils (occName, fromSrcText)
import Language.Haskell.Tools.BackendGHC.Names
import Language.Haskell.Tools.BackendGHC.Patterns (trfPattern)
import Language.Haskell.Tools.BackendGHC.Types (trfType)

import Language.Haskell.Tools.AST 
import qualified Language.Haskell.Tools.AST as AST

import Control.Monad.IO.Class

import Language.Haskell.Tools.Refactor
import Control.Monad.IO.Class
import Language.Haskell.Tools.Parser.ParseModule
import GHC.Paths ( libdir )
import Data.Generics.Uniplate.Data ()
import  Language.Haskell.Tools.Rewrite.Match.Exprs
import qualified Data.HashMap.Strict as HM
import System.IO
import Control.Monad
import qualified Data.Aeson as A
import Data.List.Extra (replace)
import Language.Haskell.Tools.Parser.SplitTypesInModule 
import Control.Exception

import Language.Haskell.Tools.AST.Representation.Binds (ULocalBind)

import Language.Haskell.Tools.Refactor as HT




-- NOTE: When working on the entire AST, we should build a monad,
--       that will will avoid unnecessary checks.
--       For example if it already found a record wildcard, it won't check again

--       Pretty easy now. Chcek wheter it is already in the ExtMap.


parseAndGetBackendFlowFunctions :: String -> IO ()
parseAndGetBackendFlowFunctions dir = do
    modules <- getAllHaskellModules dir
    moduleNames <- forM modules $ \modulePath -> do
        catch
          (getModuleName <$> readFile modulePath)
          (\(err :: SomeException) -> print (displayException err) *> pure Nothing)
    modFunHm <- foldlM appendIntoHm HM.empty $ catMaybes moduleNames
    _ <- HM.traverseWithKey (addMonitoringWrapper dir) modFunHm
    pure ()
    -- pure modFunHm 
    where 
        appendIntoHm accHm moduleName = do 
            functionsWithCount <- getFunctionsAsBackendFlow dir moduleName 
            pure $ HM.insert moduleName functionsWithCount accHm

addMonitoringWrapper :: String -> String -> [(String, Int)] -> IO ()
addMonitoringWrapper modulePath moduleName fnNamesWithCount = do 
    moduleAST <- moduleParser modulePath moduleName
    if null fnNamesWithCount  
        then do 
            print "NO Functions-----------------" 
            pure ()
        else do 
            modAST <- (!~) (biplateRef) (getModuleAndUpdate) (moduleAST)      
            newAST <- (!~) (biplateRef) (findAndReplaceFun fnNamesWithCount moduleName) (modAST)
            writeFile (modulePath Prelude.<> (replace "." "/" moduleName) Prelude.<> ".hs") (prettyPrint newAST)

getModuleAndUpdate :: Ann UModule (Dom GhcPs) SrcTemplateStage -> IO (Ann UModule (Dom GhcPs) SrcTemplateStage)
getModuleAndUpdate (Ann dom (UModule pragma head importList decl)) = pure $ (Ann dom (UModule pragma head (getAndUpdateImportList importList) decl)) 

getAndUpdateImportList :: AnnListG UImportDecl (Dom GhcPs) SrcTemplateStage -> (AnnListG UImportDecl (Dom GhcPs) SrcTemplateStage)
getAndUpdateImportList (AnnListG dom importL) = (AnnListG dom (newImpList))
    where 
        monitoringImp =
            -- mkImportDecl' False False False Nothing (mkModuleName' "Utils.Utils") (Nothing)
            --         (Just $ mkImportSpecList' [mkIESpec' (mkName' "monitorWrapper") Nothing]) 
            [mkImportDecl' False False False Nothing (mkModuleName' "EulerHS.Extra.Monitoring.Flow") (Nothing)
                    (Just $ mkImportSpecList' [mkIESpec' (mkName' "withMonitoring") Nothing])
            , mkImportDecl' False False False Nothing (mkModuleName' "NauPrelude") (Nothing)
                    (Just $ mkImportSpecList' [mkIESpec' (mkName' "(.)") Nothing])]
        newImpList = importL <> monitoringImp

getFunctionNameFromLHS :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> String
getFunctionNameFromLHS expr@(Ann _ (UNormalLhs (Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) ex1)) = ex

findAndReplaceFun :: [(String, Int)] -> String -> Ann UDecl (Dom GhcPs) SrcTemplateStage -> IO (Ann UDecl (Dom GhcPs) SrcTemplateStage)
findAndReplaceFun backendFlowFunWithCount moduleName expr@(Ann domDec valBind@(UValueBinding (Ann domValBind (UFunBind (AnnListG domFunB matchList))))) = do 
    let funWithCountHm = HM.fromList backendFlowFunWithCount
    updatedMatches <- 
        traverse 
            (\(Ann domMatch (UMatch lhsSide rhsSide binds)) -> do 
                -- let (lhsSide, rhsSide, binds, domMatch) = currMatch
                let !funName = getFunctionNameFromLHS lhsSide
                if HM.member funName funWithCountHm
                    then do 
                        case getRhsExpr rhsSide of
                            Just (oldRhsExpr, domO) -> do   
                                let newRhsExpr = mkRhsInfixExp funName moduleName oldRhsExpr
                                    rhsSideWithMonitoring = mkUnguardedRhs' $ newRhsExpr
                                    updatedMatch = (Ann domMatch (UMatch lhsSide rhsSideWithMonitoring binds))
                                    
                                pure updatedMatch
                            Nothing -> do
                                print "------------PANIC-----------------"
                                print $ "funName"
                                pure (Ann domMatch (UMatch lhsSide rhsSide binds))
                    else 
                        pure $ (Ann domMatch (UMatch lhsSide rhsSide binds))
            )
        matchList
    pure $ Ann domDec (UValueBinding (Ann domValBind (UFunBind (AnnListG domFunB updatedMatches)))) 
    -- pure (updatedValBind)
        -- else do
        --     print "-----------------------------------------------------------------------------------------\n--------------------------------------------------------------------"
        --     print funName
        --     pure expr
findAndReplaceFun _ _ expr = pure expr         
    

getMatch :: Ann UMatch (Dom GhcPs) SrcTemplateStage -> ((Ann UMatchLhs (Dom GhcPs) SrcTemplateStage), (Ann URhs (Dom GhcPs) SrcTemplateStage), (AnnMaybeG ULocalBinds (Dom GhcPs) SrcTemplateStage), (NodeInfo (SemanticInfo (Dom GhcPs) URhs) (SpanInfo SrcTemplateStage)))
getMatch (Ann dom (UMatch lhs rhs binds)) = (lhs, rhs, binds, dom)

mkRhsInfixExp :: String -> String -> (Ann UExpr (Dom GhcPs) SrcTemplateStage) -> (Ann UExpr (Dom GhcPs) SrcTemplateStage)
mkRhsInfixExp funName moduleName rhsExpr = 
    mkApp'' 
        (mkApp''  
            (mkVar' $ mkName' "withMonitoring")
            (mkLit' $ mkStringLit' $ (last modulePrefix) <> "." <> funName))
        (mkApp'' 
                (mkVar' $ mkName' "$")
                (mkParen'' rhsExpr))



    -- mkApp''
    --     (mkApp''
    --         (mkParen''
    --             ( mkApp''  
    --                 (mkVar' $ mkName' "withMonitoring")
    --                 (mkLit' $ mkStringLit' $ (last modulePrefix) <> "." <> funName)))
    --         (mkVar' $ mkName' ".")
    --     )
    --     (mkParen'' rhsExpr)
            -- (mkApp'' 
            --     (mkVar' $ mkName' "$")
                
    where
        modulePrefix = words $ map (\char -> if char == '.' then ' ' else char) moduleName

getRhsAnn :: (Ann UExpr (Dom GhcPs) SrcTemplateStage) -> (NodeInfo (SemanticInfo (Dom GhcPs) URhs) (SpanInfo SrcTemplateStage)) -> Ann URhs (Dom GhcPs) SrcTemplateStage
getRhsAnn e dom = (Ann dom (UUnguardedRhs e))


getRhsExpr :: Ann URhs (Dom GhcPs) SrcTemplateStage -> Maybe ((Ann UExpr (Dom GhcPs) SrcTemplateStage), (NodeInfo (SemanticInfo (Dom GhcPs) URhs) (SpanInfo SrcTemplateStage)))
getRhsExpr (Ann domO (UUnguardedRhs expr)) = Just (expr, domO)
getRhsExpr (Ann domO (UUnguardedRhs expr)) = Nothing
getRhsExpr _                               = Nothing 

getFunAndRhsFromUMatch :: Ann UMatch (Dom GhcPs) SrcTemplateStage -> (String, Ann URhs (Dom GhcPs) SrcTemplateStage)
getFunAndRhsFromUMatch matchBind = 
    let !funName = head $ map (getFunctionNameFromValBind) ((matchBind) ^? biplateRef)
        !rhsSide =  head $ map getRhs ((matchBind) ^? biplateRef)
    in (funName, rhsSide)
    

getRhs :: Ann URhs (Dom GhcPs) SrcTemplateStage -> Ann URhs (Dom GhcPs) SrcTemplateStage 
getRhs expr = expr

getLHS :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> Ann UMatchLhs (Dom GhcPs) SrcTemplateStage 
getLHS expr = expr


getFunctionNameFromValBind :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> String
getFunctionNameFromValBind expr@(Ann _ (UNormalLhs (Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) ex1)) = ex



getFunctionsAsBackendFlow :: String -> String -> IO [(String, Int)]
getFunctionsAsBackendFlow modulePath moduleName = do 
    moduleAST <- moduleParser modulePath moduleName
    let funNames = mapMaybe (getFunctionNames) (moduleAST ^? biplateRef)
    pure $ funNames
    
getFunctionNames :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> Maybe (String, Int)
getFunctionNames expr@(Ann _ (UTypeSigDecl (Ann _ (UTypeSignature (AnnListG _ name) _type)))) =
    let funNam = map getFunctions' name
        !funSig = map (getFunctions') ((_type) ^? biplateRef)
        funArgCount = sum $ map getFunctionCount ((_type) ^? biplateRef)
    in if any (\x -> x == "BackendFlow") funSig then Just $ (head funNam, funArgCount) else Nothing
getFunctionNames expr = Nothing

getFunctionCount :: Ann UType (Dom GhcPs) SrcTemplateStage -> Int
getFunctionCount expr@(Ann _ (UTyFun _ _)) = 1
getFunctionCount expr = 0

getFunctionDeps :: String -> String -> IO (HM.HashMap String [String])
getFunctionDeps modulePath moduleName = do
    moduleAST <- moduleParser modulePath moduleName
    print "module parsed"
    getFunctionDepOfModule moduleAST

getFunctionDepOfModule :: (Ann AST.UModule (Dom GhcPs) SrcTemplateStage) -> IO (HM.HashMap String [String])
getFunctionDepOfModule moduleAST = do
    let !funDepList = mapMaybe (traverseOverUValBind) (moduleAST ^? biplateRef)
        funList = HM.fromList $ map (\(fun,y) -> (fun, (fst y , nub $ filter (\x -> x `elem` (fst <$> funDepList)) (snd y)))) funDepList
    pure $ HM.foldlWithKey' (\acc key (x,y) -> HM.insert key (nub $ getAllRelatedFuns x y funList) acc) HM.empty funList
    where
        getAllRelatedFuns whereDeps funs funList = foldl' (\acc val -> case HM.lookup val funList of
                                                                    Just f -> acc ++ snd f
                                                                    Nothing -> acc) funs whereDeps

suffixToBeAdded :: String
suffixToBeAdded = "Split"

moduleSuffix :: String -> String
moduleSuffix modulePath = replace modulePath ".hs" ("/" ++ suffixToBeAdded) -- moduleName to be added

splitAndWrite :: String -> String -> String -> String -> IO Int
splitAndWrite modulePath moduleName groupedFunctionsString modFunReferenceString = do
    moduleAST <- moduleParser modulePath moduleName
    resolveDeps <- getFunctionDepOfModule moduleAST
    let groupedFunctions = fromMaybe (mempty) (A.decode $ A.encode groupedFunctionsString)  
    let modFunReference = fromMaybe (mempty) (A.decode $ A.encode modFunReferenceString)  
    writeBackGroupedModules modulePath moduleName resolveDeps moduleAST groupedFunctions modFunReference

writeBackGroupedModules :: String -> String -> HM.HashMap String [String] -> (Ann AST.UModule (Dom GhcPs) SrcTemplateStage) -> [[String]] -> HM.HashMap String Int -> IO Int
writeBackGroupedModules modulePath moduleName resolveDeps moduleAST groupedFunctions modFunReference = do
    -- fun list generated by python
    (AST.AnnListG annot currentDecl) <- moduleAST ^? (modDecl) 
    let newImportsList = map nub $ snd $ foldl' (\(l,acc) fun -> (l+1,acc ++ [foldl' (\(acc) x -> maybe (acc) (\val -> ((fetchNum val l) ++ acc)) $ HM.lookup x resolveDeps) ([]) fun])) (0,[]) groupedFunctions
    !newModDecl <- mapM (\(x,y) -> do
                            let decls = filter (\decl -> checkFun decl x) currentDecl
                                nAST = (.=) modDecl (AST.AnnListG annot decls) moduleAST
                            impsFil <- ((\(AST.AnnListG annot val) -> pure $ modifyImports y val) =<< (nAST ^? modImports)) --(.=) modDecl (AST.AnnListG annot decls) nAST
                            pure $ (.=) modImports (AST.AnnListG annot impsFil) nAST
                        ) (zip groupedFunctions newImportsList) 
    let newModDeclForRoot = let decls = filter (\decl -> not $ checkFun decl (concat groupedFunctions)) currentDecl
                                in (.=) modDecl (AST.AnnListG annot decls) moduleAST
    writeFile modulePath  (prettyPrint newModDeclForRoot)
    foldM (\acc x -> do
        changedModName <- liftIO $ (!~) (biplateRef) (changeModName (("." ++ suffixToBeAdded) ++ (show acc))) (x)
        (writeFile ((moduleSuffix modulePath) ++ (show acc) ++ ".hs") (prettyPrint changedModName))
        pure $ (acc + 1)) 0 newModDecl

    where
        modifyImports :: [String] -> [Ann UImportDecl (Dom GhcPs) SrcTemplateStage] -> [Ann UImportDecl (Dom GhcPs) SrcTemplateStage]
        modifyImports imps val =  foldl' (\(acc) x ->  ( acc ++ [mkImportDecl' False False False Nothing (mkModuleName' x) Nothing Nothing])) (val) imps
        fetchNum :: [String] -> Int -> [String]
        fetchNum val l = foldl' (\(acc) x -> maybe (acc) (\y -> if l == y then acc else ([moduleName ++ suffixToBeAdded ++ (show y)] ++ acc)) $ HM.lookup x modFunReference) [] val


changeModName :: String -> Ann UModuleHead (Dom GhcPs) SrcTemplateStage -> IO (Ann UModuleHead (Dom GhcPs) SrcTemplateStage)
changeModName str expr@(Ann y ((UModuleHead (Ann b (UModuleName name)) prag (AnnMaybeG x _)))) = do
   let names = name ++ str
   print names
   let modName = mkModuleName' names
   let modHead = mkModuleHead' modName Nothing Nothing
   pure modHead


checkFun :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> [String] -> Bool
checkFun expr@(Ann _ (UTypeSigDecl (Ann _ (UTypeSignature funName _)))) str = any (== (head $ map getFunctions' $ funName ^? biplateRef)) str
checkFun expr@(Ann _ (UValueBinding (FunctionBind' ex))) str =
    let !funName = map (getFunctionNameFromValBind) ((ex) ^? biplateRef)
    in any (== head funName) str
checkFun _ _ = False

traverseOverUValBind :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> Maybe (String, ([String],[String]))
traverseOverUValBind expr@(Ann _ (UValueBinding (FunctionBind' ex))) = do
    let !funName = map (getFunctionNameFromValBind) ((ex) ^? biplateRef)
    let !funNameMap = (head funName, tail funName)
    let !funDeps = concat $ map (getFunctionsCalledInFunction) (expr ^? biplateRef)
    Just (head funName, (tail funName, funDeps))
traverseOverUValBind expr = Nothing


getFunctionsCalledInFunction :: Ann URhs (Dom GhcPs) SrcTemplateStage -> [String]
getFunctionsCalledInFunction expr = do
    let !funs = filter (/= "") $ map (getFunctions') ((expr ^? biplateRef))
    funs

getFunctions' :: Ann UName (Dom GhcPs) SrcTemplateStage -> String
getFunctions' expr@(Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) = ex
getFunctions' expr = ""

