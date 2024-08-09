{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables, PartialTypeSignatures #-}

module Language.Haskell.Tools.Parser.RemoveExceptionsInGatewaySyncFn where

import Language.Haskell.Tools.Refactor as Refactor hiding (LambdaCase)
import Language.Haskell.Tools.Refactor.Utils.Extensions
import Language.Haskell.Tools.Rewrite.Match.Binds
import Control.Monad.Reader
import Control.Monad.State
import Control.Concurrent.MVar
import GHC hiding (Name, mkModuleName)
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
import Data.Char (isAlphaNum, toLower)
import Data.Function (on)
import Data.Maybe (mapMaybe)
import Data.List
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
import Language.Haskell.Tools.Parser.ParseModule hiding (getFunctionName)
import GHC.Paths ( libdir )
import Data.Generics.Uniplate.Data ()
import  Language.Haskell.Tools.Rewrite.Match.Exprs
import qualified Data.HashMap.Strict as HM
import System.IO
import Control.Monad
import qualified Data.Aeson as A
import Data.List.Extra (replace, foldl, splitOn, stripSuffix)
import System.Directory
import System.IO.Unsafe
import Language.Haskell.Tools.Refactor as HT
import Language.Haskell.Tools.Rewrite.Create.Utils (mkAnnList')
import Language.Haskell.Tools.AST.Representation.Binds (ULocalBind)
-- import Language.Haskell.Tools.Parser.GetFunctionBranching (parseImportsAndGetModule)

projectPath :: String
projectPath = "/Users/sandeep.palla/Desktop/one-team-fixes/euler-api-txns"

getModulePath :: String
getModulePath = "/Users/sandeep.palla/Desktop/one-team-fixes/euler-api-txns/euler-x/src-generated/"

getModuleName :: String
getModuleName = "Gateway.PhonePe.Flow"

type SyncFunctionName = String
type SyncResponseSumType = String
type SyncErrorTypeToBeUsed = String

data InputData = InputData
  { syncFunctionName  :: String
  , typeToBeUsedForOp :: String
  }

getInputData :: [InputData]
getInputData =
  [ (InputData "phonepeTxnSync" "TransactionStatusResponse")
  , (InputData "phonepeAuthSync" "TransactionStatusResponse")
  ]

exceptionFuncList :: [String]
exceptionFuncList =
  [ "defaultThrowECException"
  , "throwUpstreamGatewayError"
  , "defaultInvalidThrowECException"
  , "throwErr"
  ]

removeExceptions :: IO _
removeExceptions =
  mapM (replaceExceptions getModulePath getModuleName) getInputData

replaceExceptions :: String -> String -> InputData -> IO _
replaceExceptions modulePath moduleName inputData = do
  moduleAST <- moduleParser modulePath moduleName
  (AST.AnnListG annot currentDecl) <- moduleAST ^? (modDecl)
  decls <-
    foldM
      (\acc decl -> do
        if getGivenFun (syncFunctionName inputData) decl
          then do
            changedFuns <- replaceThrowErrInDecl decl
            pure $ acc ++ changedFuns
          else
            pure $ acc ++ [decl]
      )
      []
      currentDecl
  let groupedDecls = decls
  let nAST = (.=) modDecl (AST.AnnListG annot groupedDecls) moduleAST
  writeFile (modulePath <> (replace "." "/" moduleName) <> ".hs") (prettyPrint nAST)

  if (syncFunctionName (head getInputData)) == (syncFunctionName inputData)
    then do
      let syncDecl = head $ filter (\x -> getRequiredFun x (syncFunctionName inputData)) currentDecl
          syncSign = head $ filter (\x -> getRequiredFunSign x (syncFunctionName inputData)) currentDecl

      -- An ugly way to create a function but okayy!
      newFuncDef <- (!~) (biplateRef) (changeNameToReqFun (syncFunctionName inputData) "\ngetResponseForSyncFailureCaseHandling") (syncSign)
      newFuncDef <- (!~) (biplateRef) (getNewFunctionTypeSigArgs (typeToBeUsedForOp inputData)) newFuncDef
      newFuncImp <- (!~) (biplateRef) (getNewFuncLhs) (syncDecl)
      newFuncImp <- (!~) (biplateRef) (getNewFuncRhs) newFuncImp
      --

      tfModuleAST <- moduleParser modulePath (replace "Flow" "Transforms" moduleName)
      (AST.AnnListG tfAnnot tfCurrentDecl) <- tfModuleAST ^? (modDecl)
      let nTfAST = (.=) modDecl (AST.AnnListG tfAnnot (tfCurrentDecl ++ [newFuncDef, newFuncImp])) tfModuleAST
      writeFile (modulePath <> (replace "." "/" (replace "Flow" "Transforms" moduleName)) <> ".hs") (prettyPrint nTfAST)
    else
      pure ()

replaceThrowErrInDecl :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> IO [(Ann UDecl (Dom GhcPs) SrcTemplateStage)]
replaceThrowErrInDecl (Ann ann (UValueBinding binds)) = do
  updBinds <- replaceInValueBind binds
  let res = Ann ann $ UValueBinding updBinds
  pure [res]
replaceThrowErrInDecl decl = pure [decl]

getNewFuncLhs :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> IO (Ann UMatchLhs (Dom GhcPs) SrcTemplateStage)
getNewFuncLhs _ = pure $ mkMatchLhs' (mkName' "getResponseForSyncFailureCaseHandling") []

getNewFuncRhs :: Ann UMatch (Dom GhcPs) SrcTemplateStage -> IO (Ann UMatch (Dom GhcPs) SrcTemplateStage)
getNewFuncRhs expr@(Ann _ (UMatch lhs _ _)) = pure $ mkMatchForRanged lhs (mkUnguardedRhs' $ mkVar' $ mkName' "undefined") Nothing

getNewFunctionTypeSigArgs :: String -> Ann UType (Dom GhcPs) SrcTemplateStage -> IO (Ann UType (Dom GhcPs) SrcTemplateStage)
getNewFunctionTypeSigArgs typeName _ = pure $ mkVarTypeForRanged $ mkName' typeName

replaceInValueBind :: Ann UValueBind (Dom GhcPs) SrcTemplateStage -> IO (Ann UValueBind (Dom GhcPs) SrcTemplateStage)
replaceInValueBind (Ann a1 (UFunBind (AnnListG a2 matches))) = do
  updMatch <- mapM replaceInMatch matches
  pure $ Ann a1 $ UFunBind (AnnListG a2 updMatch)
replaceInValueBind valueBind = pure valueBind

replaceInMatch :: Ann UMatch (Dom GhcPs) SrcTemplateStage -> IO (Ann UMatch (Dom GhcPs) SrcTemplateStage)
replaceInMatch (Ann a1 (UMatch lhs rhs binds)) = do
  updBinds <- replaceWhereBinds binds
  updRhs <- replaceRhsExpr rhs
  pure $ Ann a1 (UMatch lhs updRhs updBinds)

replaceRhsExpr :: Ann URhs (Dom GhcPs) SrcTemplateStage -> IO (Ann URhs (Dom GhcPs) SrcTemplateStage)
replaceRhsExpr (Ann ann (UUnguardedRhs expr)) = do
  updExpr <- replaceInExpr expr
  pure $ Ann ann $ UUnguardedRhs updExpr
-- replaceRhsExpr (Ann ann (GuardedRhss rhss)) = Ann ann $ GuardedRhss (map replaceInGuardedRhs (rhss ^. annList))
replaceRhsExpr expr = pure expr

-- replaceInGuardedRhs :: Ann UGuardedRhs (Dom GhcPs) SrcTemplateStage -> Ann UGuardedRhs (Dom GhcPs) SrcTemplateStage
-- replaceInGuardedRhs (Ann ann (UGuardedRhs guards expr)) =
--   Ann ann $ UGuardedRhs (map replaceInStmt (guards ^. annList)) (replaceInExpr expr)

replaceWhereBinds :: AnnMaybeG ULocalBinds (Dom GhcPs) SrcTemplateStage -> IO (AnnMaybeG ULocalBinds (Dom GhcPs) SrcTemplateStage)
replaceWhereBinds (AnnMaybeG a1 (Just (Ann ann (ULocalBinds binds)))) = do
  updBinds <- replaceInLocalBindsL binds
  pure $ AnnMaybeG a1 (Just (Ann ann (ULocalBinds updBinds)))
replaceWhereBinds expr = pure expr

replaceInLocalBindsL :: AnnListG ULocalBind (Dom GhcPs) SrcTemplateStage -> IO (AnnListG ULocalBind (Dom GhcPs) SrcTemplateStage)
replaceInLocalBindsL (AnnListG a1 decs) = do
  updDecs <- mapM replaceInLocalBinds decs
  pure $ AnnListG a1 updDecs

replaceInLocalBinds :: Ann ULocalBind (Dom GhcPs) SrcTemplateStage -> IO (Ann ULocalBind (Dom GhcPs) SrcTemplateStage)
replaceInLocalBinds (Ann ann (ULocalValBind binds)) = do
  updBinds <- replaceInValueBind binds
  pure $ Ann ann $ ULocalValBind updBinds
replaceInLocalBinds expr = pure expr

replaceInExpr :: Ann UExpr (Dom GhcPs) SrcTemplateStage -> IO (Ann UExpr (Dom GhcPs) SrcTemplateStage)
replaceInExpr (Ann ann (UApp fun args)) = do
  -- print ("reached[UApp]")
  -- print (Ann ann (UApp fun args))
  if isThrowErr fun
    then pure $ mkVar' $ mkName' "undefined"
    else do
      updFn <- replaceInExpr fun
      updArgs <- replaceInExpr args
      pure $ Ann ann (UApp updFn updArgs)
replaceInExpr (Ann ann (UInfixApp left op right)) = do
  -- print ("reached[UInfixApp]")
  -- print (Ann ann (UInfixApp left op right))
  if isDollarOperator op && isThrowErr left
    then pure $ mkVar' $ mkName' "undefined"
    else do
      updLeft <- replaceInExpr left
      updRight <- replaceInExpr right
      pure $ Ann ann $ UInfixApp updLeft op updRight
replaceInExpr (Ann ann (UParen expr)) = do
  -- print ("reached[UParen]")
  -- print (Ann ann (UParen expr))
  updExpr <- replaceInExpr expr
  pure $ Ann ann $ UParen updExpr
replaceInExpr (Ann ann (UCase expr (AnnListG a2 alts))) = do
  -- print ("reached[UCase]")
  -- print (Ann ann (UCase expr (AnnListG a2 alts)))
  updExpr <- replaceInExpr expr
  updAlts <- mapM replaceInAlt alts
  pure $ Ann ann $ UCase updExpr (AnnListG a2 updAlts)
replaceInExpr (Ann ann (UIf cond thenExpr elseExpr)) = do
  -- print ("reached[UIf]")
  -- print (Ann ann (UIf cond thenExpr elseExpr))
  updCondtion <- replaceInExpr cond
  updThenExpr <- replaceInExpr thenExpr
  updElseExpr <- replaceInExpr elseExpr
  pure $ Ann ann $ UIf updCondtion updThenExpr updElseExpr
replaceInExpr (Ann ann (ULet binds expr)) = do
  -- print ("reached[ULet]")
  -- print (Ann ann (ULet binds expr))
  updBindsL <- replaceInLocalBindsL binds
  updExpr <- replaceInExpr expr
  pure $ Ann ann $ ULet updBindsL updExpr
replaceInExpr (Ann ann (UDo kind (AnnListG a2 stmts))) = do
  -- print ("reached[UDo]")
  -- print (Ann ann (UDo kind (AnnListG a2 stmts)))
  updStmts <- mapM replaceInStmt stmts
  pure $ Ann ann $ UDo kind (AnnListG a2 updStmts)
replaceInExpr expr = do
  -- print ("reached[MatchFailed]")
  -- print expr
  pure expr

replaceInAlt :: Ann UAlt (Dom GhcPs) SrcTemplateStage -> IO (Ann UAlt (Dom GhcPs) SrcTemplateStage)
replaceInAlt (Ann ann (UAlt pat rhs binds)) = do
  updRhs <- replaceRhsInAlt rhs
  updBinds <- replaceWhereBinds binds
  pure $ Ann ann $ UAlt pat updRhs updBinds

replaceRhsInAlt :: Ann UCaseRhs (Dom GhcPs) SrcTemplateStage -> IO (Ann UCaseRhs (Dom GhcPs) SrcTemplateStage)
replaceRhsInAlt (Ann a1 (UUnguardedCaseRhs expr)) = do
  updExpr <- replaceInExpr expr
  pure $ Ann a1 (UUnguardedCaseRhs updExpr)
replaceRhsInAlt expr = do
  pure expr

replaceInStmt :: Ann UStmt (Dom GhcPs) SrcTemplateStage -> IO (Ann UStmt (Dom GhcPs) SrcTemplateStage)
replaceInStmt (Ann ann (UBindStmt pat expr)) = do
  updExpr <- replaceInExpr expr
  pure $ Ann ann $ UBindStmt pat updExpr
replaceInStmt (Ann ann (ULetStmt binds)) = do
  updBindsL <- replaceInLocalBindsL binds
  pure $ Ann ann $ ULetStmt updBindsL
replaceInStmt (Ann ann (UExprStmt expr)) = do
  updExpr <- replaceInExpr expr
  pure $ Ann ann (UExprStmt updExpr)
replaceInStmt stmt = pure stmt

isThrowErr :: Ann UExpr (Dom GhcPs) SrcTemplateStage -> Bool
isThrowErr (Ann _ (UVar (Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart name)))))))) = elem name exceptionFuncList
isThrowErr (Ann _ (UApp fun arg)) = isThrowErr fun
isThrowErr _ = False

isDollarOperator :: Ann UOperator (Dom GhcPs) SrcTemplateStage -> Bool
isDollarOperator (Ann _ (UNormalOp (Ann _ (UQualifiedName _ (Ann _ (UNamePart name)))))) = name == "$"
isDollarOperator _ = False

getRequiredFun :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> String -> Bool
getRequiredFun expr@(Ann _ (UValueBinding (FunctionBind' ex))) fun =
  let !funName = mapMaybe (getFunctionNameFromValBind) ((ex) ^? biplateRef)
  in if null funName then False else any (== fun) funName
getRequiredFun _ _ = False

getRequiredFunSign :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> String -> Bool
getRequiredFunSign (Ann _ (UTypeSigDecl (Ann _ (UTypeSignature (AnnListG _ names) tsType)))) fun =
  any (\name -> getNamePart name == Just fun) names
getRequiredFunSign _ _ = False

getGivenFun :: String -> Ann UDecl (Dom GhcPs) SrcTemplateStage -> Bool
getGivenFun expectedFun expr@(Ann _ (UTypeSigDecl (Ann _ (UTypeSignature (AnnListG _ names) _)))) = any (\name -> getNamePart name == Just expectedFun) names
getGivenFun expectedFun expr@(Ann _ (UValueBinding (FunctionBind' ex))) =
    let !funName = mapMaybe (getFunctionNameFromValBind) ((ex) ^? biplateRef)
    in if null funName then False else any (== expectedFun) funName
getGivenFun _ _ = False

getFunctionNameFromValBind :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> Maybe String
getFunctionNameFromValBind expr@(Ann _ (UNormalLhs (Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) ex1)) = Just ex
getFunctionNameFromValBind _ = Nothing

getNamePart :: Ann UName (Dom GhcPs) SrcTemplateStage -> Maybe String
getNamePart expr@(Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) = Just ex
getNamePart expr = Nothing

changeNameToReqFun :: String -> String -> Ann UName (Dom GhcPs) SrcTemplateStage -> IO (Ann UName (Dom GhcPs) SrcTemplateStage)
changeNameToReqFun org new expr@(Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) = 
    pure $ if ex == org then mkName' new else expr
changeNameToReqFun _ _ expr = pure expr
