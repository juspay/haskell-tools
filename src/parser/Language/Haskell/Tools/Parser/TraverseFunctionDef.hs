{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables, PartialTypeSignatures #-}

module Language.Haskell.Tools.Parser.TraverseFunctionDef where

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
import Data.List (nub)
-- import Language.Haskell.Tools.Parser.GetFunctionBranching (parseImportsAndGetModule)



testProjectPath :: String
testProjectPath = "/Users/yashasvi.rana/Documents/Other Repos/haskell-tools/src/parser"

testModuleName :: String
testModuleName = "Language.Haskell.Tools.Parser.Test"

isLog :: Bool
isLog = True

appendResult :: String -> IO _
appendResult = appendFile "outputlog.txt"

logText :: String -> IO _
logText str = if isLog
  then putStr str
  else pure ()

-- example of how to get all possible functions that can be called, when `payUTxnSync` gets called
proxy :: IO _
proxy = do
    moduleAST <- moduleParser testProjectPath testModuleName
    funcs <- getAllFunctions moduleAST "olaTxnSync" []
    writeFile "output.txt" $ show funcs

getFunctionsFromList :: Ann UModule (Dom GhcPs) SrcTemplateStage -> [String] -> [String] -> IO [String]
getFunctionsFromList moduleAST [] functionsDone = return functionsDone
getFunctionsFromList moduleAST (functionName : functionNames) functionsDone = do
    done <- getAllFunctions moduleAST functionName functionsDone
    rest <- getFunctionsFromList moduleAST functionNames (nub (done ++ functionsDone))
    return (nub (done ++ rest))

-- This may break if there are multiple funcitons in a module with the same name or functions with same name in different where blocks
getAllFunctions :: Ann UModule (Dom GhcPs) SrcTemplateStage -> String -> [String] -> IO [String]
getAllFunctions moduleAST functionName functionsDone = do
    decls@(AnnListG _ currentDecl) <- moduleAST ^? (modDecl)

    let 
        newfunctionsDone = nub (functionName : functionsDone)
        funcs = getFunctionsCalled decls functionName
        newFuncs = filter (`notElem` newfunctionsDone) funcs
        allDoneFuncs = newFuncs ++ newfunctionsDone

    appendResult $ (show (functionName) ++ "\n functions called: " ++ show funcs ++ "\n")
    if length newFuncs > 0
        then do
            temp <- getFunctionsFromList moduleAST newFuncs functionsDone 
            return $ nub (temp ++ allDoneFuncs)
        else
            return $ allDoneFuncs
    

getFunctionsCalled :: AnnListG UDecl (Dom GhcPs) SrcTemplateStage -> String -> [String]
getFunctionsCalled (AnnListG _ currentDecl) functionName =
    let temp1 = filter
                (\decl -> getGivenFun functionName decl)
                currentDecl
        temp = if length temp1 > 0
                then
                    tail temp1
                else 
                    []
    in
        if length temp > 0
            then
                let
                    decls = head temp
                    funcs = nub $ stateUDecl decls []
                    moduleFuncs = filter (\name -> (any (\decl -> getGivenFun name decl) currentDecl)) funcs
                in
                    moduleFuncs
            else
                []


stateULocalBind :: Ann ULocalBind (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateULocalBind (Ann _ (ULocalValBind valBind)) funcs = stateUValueBind valBind funcs
stateULocalBind _ funcs = funcs

stateUGuardedCaseRhs :: Ann UGuardedCaseRhs (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUGuardedCaseRhs (Ann _ (UGuardedCaseRhs (AnnListG _ statements) expr)) funcs = let
  funcs1 = saveFromList stateURhsGuard statements funcs
  funcs2 = stateUExpr expr funcs
  in funcs1 ++ funcs2

stateUCaseRhs :: Ann UCaseRhs (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUCaseRhs (Ann _ rhs) funcs = 
  case rhs of 
    (UUnguardedCaseRhs expr) -> stateUExpr expr funcs
    (UGuardedCaseRhss (AnnListG _ exprs)) -> saveFromList stateUGuardedCaseRhs exprs funcs

stateUAlt :: Ann UAlt (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUAlt (Ann _ (UAlt pattern caseRhs (AnnMaybeG _ binds))) funcs = let
  f1 = stateUPattern pattern funcs
  f2 = stateUCaseRhs caseRhs funcs
  f3 = f1 ++ f2
  in
    case binds of
        Just (Ann _ (ULocalBinds (AnnListG _ binds))) -> f3 ++ saveFromList stateULocalBind binds funcs
        Nothing -> f3

stateUStmt :: Ann UStmt (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUStmt (Ann _ statement) funcs = 
  case statement of
    (UBindStmt pattern expr) -> let
      f1 = stateUPattern pattern funcs
      f2 = stateUExpr expr funcs
      in
        f1 ++ f2
    (UExprStmt expr) -> stateUExpr expr funcs
    (ULetStmt (AnnListG _ binds)) -> saveFromList stateULocalBind binds funcs
    (URecStmt (AnnListG _ statements)) -> saveFromList stateUStmt statements  funcs


stateUExpr :: Ann UExpr (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUExpr (Ann _ expr) funcs = 
  case expr of
    (UVar funName) -> (fromMaybe "Nothing" $ getNamePart funName) : funcs 
    (UApp (Ann _ (UVar funName)) arg) -> (fromMaybe "Nothing" $ getNamePart funName) : funcs
    (UApp fun arg) -> let
      f1 = stateUExpr fun funcs
      in
        stateUExpr arg f1
    (UInfixApp lhs op rhs) -> let
      f1 = stateUExpr lhs funcs
      in
        stateUExpr rhs f1
    (UPrefixApp (Ann _ op) rhs) -> let
      f1 = show op : funcs
      in
        stateUExpr rhs f1
    (ULambda _ expr) -> stateUExpr expr funcs
    (ULet (AnnListG _ binds) expr) -> let
      f1 = saveFromList stateULocalBind binds funcs
      in
        stateUExpr expr f1
    (UIf condExpr thenExpr elseExpr) -> let
      f1 = stateUExpr condExpr funcs
      f2 = stateUExpr thenExpr f1
      in
        stateUExpr elseExpr f2
    (UMultiIf (AnnListG _ uGcases)) -> saveFromList stateUGuardedCaseRhs uGcases funcs
    (UCase expr (AnnListG _ alts)) -> let
      f1 = stateUExpr expr funcs
      in
        saveFromList stateUAlt alts f1
    (UDo _ (AnnListG _ statements)) -> saveFromList stateUStmt statements funcs
    (UParen expr) -> stateUExpr expr funcs
    (ULeftSection expr op) -> stateUExpr expr funcs
    (URightSection op expr) -> stateUExpr expr funcs
    _ -> funcs

-- Patterns of LHS of assignments
stateUPattern :: Ann UPattern (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUPattern (Ann _ (_)) funcs = funcs


stateURhsGuard :: Ann URhsGuard (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateURhsGuard (Ann _ (UGuardBind pattern rhsExpr)) funcs = let
  f1 = stateUPattern pattern funcs
  f2 = stateUExpr rhsExpr funcs
  in 
    f1 ++ f2
stateURhsGuard (Ann _ (UGuardLet (AnnListG _ binds))) funcs = saveFromList stateULocalBind binds funcs
stateURhsGuard (Ann _ (UGuardCheck checkExpr)) funcs = stateUExpr checkExpr funcs


stateUGuardedRhs :: Ann UGuardedRhs (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUGuardedRhs (Ann _ (UGuardedRhs (AnnListG _ statements) expr)) funcs = let
  f1 = saveFromList stateURhsGuard statements funcs
  f2 = stateUExpr expr funcs
  in
    f1 ++ f2

stateURhs :: Ann URhs (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateURhs (Ann _ (UUnguardedRhs expr)) = stateUExpr expr
stateURhs (Ann _ (UGuardedRhss (AnnListG _ exprs))) = saveFromList stateUGuardedRhs exprs

stateUMatch :: Ann UMatch (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUMatch (Ann _ (UMatch _lhs rhs (AnnMaybeG _ mbinds))) funcs = let
  f1 = stateURhs rhs funcs
  in
    case mbinds of
        Just (Ann _ (ULocalBinds (AnnListG _ binds))) -> saveFromList stateULocalBind binds f1
        Nothing -> f1

stateUValueBind :: Ann UValueBind (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUValueBind (Ann _ (USimpleBind _ rhs (AnnMaybeG _ mBinds))) funcs = let
  f1 = stateURhs rhs funcs
  in
    case mBinds of
        Just (Ann _ (ULocalBinds (AnnListG _ binds))) -> saveFromList stateULocalBind binds f1
        Nothing -> f1
stateUValueBind (Ann _ (UFunBind (AnnListG _ matches))) funcs = saveFromList stateUMatch matches funcs

stateUDecl :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> [String] -> [String]
stateUDecl (Ann _ (UValueBinding valBind)) funcs = stateUValueBind valBind funcs
stateUDecl (Ann _ _decl) funcs = funcs

saveFromList :: (a -> [String] -> [String]) -> [a] -> [String] -> [String]
saveFromList _ [] funcs = funcs
saveFromList fun (element : remaining) funcs = let
      f1 = fun element funcs
      in
        saveFromList fun remaining f1


-- Functoins from RemoveExceptionsInGatewaySyncFn to avoid cyclic imports --

getGivenFun :: String -> Ann UDecl (Dom GhcPs) SrcTemplateStage -> Bool
getGivenFun expectedFun expr@(Ann _ (UTypeSigDecl (Ann _ (UTypeSignature (AnnListG _ names) _)))) = any (\name -> getNamePart name == Just expectedFun) names
getGivenFun expectedFun expr@(Ann _ (UValueBinding (FunctionBind' ex))) =
    let !funName = mapMaybe (getFunctionNameFromValBind) ((ex) ^? biplateRef)
    in if null funName then False else any (== expectedFun) funName
getGivenFun _ _ = False

getNamePart :: Ann UName (Dom GhcPs) SrcTemplateStage -> Maybe String
getNamePart expr@(Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) = Just ex
getNamePart expr = Nothing

getFunctionNameFromValBind :: Ann UMatchLhs (Dom GhcPs) SrcTemplateStage -> Maybe String
getFunctionNameFromValBind expr@(Ann _ (UNormalLhs (Ann _ (UNormalName (Ann _ (UQualifiedName _ (Ann _ (UNamePart ex)))))) ex1)) = Just ex
getFunctionNameFromValBind _ = Nothing