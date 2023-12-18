{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Tools.Parser.SplitTypesInModule where

import Control.Reference
import Data.List.Extra (nub,find,splitOn,replace,isInfixOf)
import qualified Data.List
import Data.Maybe (mapMaybe,maybeToList,catMaybes)
import GHC
import Language.Haskell.Tools.AST
import Language.Haskell.Tools.Parser.ParseModule
import qualified Data.Aeson as A
import qualified Data.Bifunctor as BI
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import System.Directory (doesDirectoryExist, getDirectoryContents)
import System.FilePath (takeExtension, (</>))
import Control.Monad (forM)
import Control.Exception
import Data.List (foldl')

-- NOTE: Looking for only types file
isHaskellFile :: FilePath -> Bool
isHaskellFile file = takeExtension file == ".hs"

getAllHaskellModules :: FilePath -> IO [FilePath]
getAllHaskellModules dir = do
  contents <- getDirectoryContents dir
  print $ show contents 
  -- undefined
  let files = filter (\f -> f /= "." && f /= "..") contents
  paths <- forM files $ \file -> do
    let path = dir System.FilePath.</> file
    isDir <- doesDirectoryExist path
    if isDir
      then getAllHaskellModules path
      else return [path | isHaskellFile path]
  return (concat paths)

getModuleName :: String -> Maybe String
getModuleName content = do
    let moduleLine = find ("module" `Data.List.isPrefixOf`) (lines content)
    (Just . head . splitOn " " . replace "module " "" . replace " where" "") =<< moduleLine

getAllTypesInProject :: String -> IO () 
getAllTypesInProject dir = do
    modules <- getAllHaskellModules dir
    moduleNames <- forM modules $ \modulePath -> do
        catch
          (getModuleName <$> readFile modulePath)
          (\(err :: SomeException) -> print (displayException err) *> pure Nothing)
    print (moduleNames)
    res <- mapM (\x -> parseAndGenerateBuckets dir x) $ catMaybes moduleNames
    writeFile ("types_graph.json") (show $ A.encode $ Data.List.foldl' (\acc hm -> addHashMap acc hm) HM.empty $ res) 
    where 
        addHashMap hmg hm = 
            Data.List.foldl' (\acc (k,v) -> 
                let val = 
                        case HM.lookup k acc of
                            Just vg -> nub $ (vg ++ v)
                            Nothing -> v 
                in HM.insert k val acc
            ) hmg $ HM.toList hm

findConnectedComponents :: HM.HashMap String [String] -> [[String]]
findConnectedComponents graph =
  let allNodes = HM.keys graph
      visitedNodes = HS.empty
      (_, components) = foldl (processNode graph) (visitedNodes, []) allNodes
  in components
 where
    processNode :: HM.HashMap String [String] -> (HS.HashSet String, [[String]]) -> String -> (HS.HashSet String, [[String]])
    processNode graph (visitedNodes, components) node
      | HS.member node visitedNodes = (visitedNodes, components)
      | otherwise =
        let connectedComponent = dfsConnectedComponent graph node visitedNodes
        in (visitedNodes `HS.union` HS.fromList connectedComponent, connectedComponent : components)

    dfsConnectedComponent :: HM.HashMap String [String] -> String -> HS.HashSet String -> [String]
    dfsConnectedComponent graph currentNode visitedNodes =
      case HM.lookup currentNode graph of
        Just neighbors ->
          let unvisitedNeighbors = filter (\x -> not $ x `HS.member` visitedNodes) neighbors
          in currentNode : concatMap (\neighbor -> dfsConnectedComponent graph neighbor (HS.insert neighbor visitedNodes)) unvisitedNeighbors
        Nothing -> [currentNode]

splitOneTypeFileIntoMany :: String -> String -> IO [[[String]]]
splitOneTypeFileIntoMany modulePath moduleName = do
    typeData <- parseAndGenerateBuckets modulePath moduleName
    let components = findConnectedComponents typeData
        minNoOfFiles = ((length components) `div` 25)
    pure $ splitIntoNSublists minNoOfFiles $ components
    where
        splitIntoNSublists :: Int -> [a] -> [[a]]
        splitIntoNSublists _ [] = []
        splitIntoNSublists n list =
          let (sublist, rest) = splitAt n list
          in sublist : splitIntoNSublists n rest

parseAndGenerateBuckets :: String -> String -> IO (HM.HashMap String [String])
parseAndGenerateBuckets modulePath moduleName = do
    moduleAST <- moduleParser modulePath moduleName
    pure $ HM.fromList $ map (BI.second nub) $ mapMaybe getTypeData (moduleAST ^? biplateRef)

getTypeData :: Ann UDecl (Dom GhcPs) SrcTemplateStage -> Maybe (String,[String])
-- getTypeData expr@(Ann _ (UTypeDecl declHead declType)) = (\x -> Just (x,getAllField declType)) =<< getNameFromDeclHead declHead
getTypeData (Ann _ (UDataDecl _ _ declHead declCons _)) = (\x -> Just (x,extractUConDeclFromAnnListG declCons)) =<< getNameFromDeclHead declHead
getTypeData _ = Nothing

getNameFromDeclHead :: Ann UDeclHead (Dom GhcPs) SrcTemplateStage -> Maybe String
getNameFromDeclHead (Ann _ (UDeclHead uName)) = extractNameFromUName uName
getNameFromDeclHead _ = Nothing

extractUConDeclFromAnnListG :: AnnListG UConDecl (Dom GhcPs) SrcTemplateStage -> [String]
extractUConDeclFromAnnListG (AnnListG _ elems) = concatMap getAllField elems

getAllField :: Ann UConDecl (Dom GhcPs) SrcTemplateStage -> [String]
getAllField (Ann _ (UConDecl _ _ _ conDeclArgs)) = (\(AnnListG _ elems) -> mapMaybe (\(Ann _ x) -> extractNameFromUTyVar x) elems) conDeclArgs
getAllField (Ann _ (URecordDecl _ _ _ conDeclFields)) = (\(AnnListG _ elems) -> concatMap getAllFieldType elems) conDeclFields
getAllField (Ann _ (UInfixConDecl _ _ _ _ _)) = []

getAllFieldType :: Ann UFieldDecl (Dom GhcPs) SrcTemplateStage -> [String]
getAllFieldType (Ann _ (UFieldDecl _ (Ann _ (UTyApp _ ((Ann _ uType)))))) = maybeToList $ extractNameFromUTyVar uType
getAllFieldType (Ann _ (UFieldDecl _ (Ann _ uType))) = maybeToList $ extractNameFromUTyVar uType

extractNameFromUTyVar :: UType (Dom GhcPs) SrcTemplateStage -> Maybe String
extractNameFromUTyVar (UTyVar uName) = extractNameFromUName uName
extractNameFromUTyVar _ = Nothing

extractNameFromUName :: Ann UName (Dom GhcPs) SrcTemplateStage -> Maybe String
extractNameFromUName (Ann _ (UParenName (Ann _(UQualifiedName _ (Ann _ (UNamePart ex)))))) = Just ex
extractNameFromUName (Ann _ (UNormalName (Ann _(UQualifiedName _ (Ann _ (UNamePart ex)))))) = Just ex
extractNameFromUName (Ann _ (UImplicitName (Ann _(UQualifiedName _ (Ann _ (UNamePart ex)))))) = Just ex