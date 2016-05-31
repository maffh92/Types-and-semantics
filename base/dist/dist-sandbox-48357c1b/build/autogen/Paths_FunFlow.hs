module Paths_FunFlow (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,2,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "D:\\Development\\School\\Types and Semantic\\Types-and-semantics\\base\\.cabal-sandbox\\bin"
libdir     = "D:\\Development\\School\\Types and Semantic\\Types-and-semantics\\base\\.cabal-sandbox\\i386-windows-ghc-7.8.3\\FunFlow-0.2.0.0"
datadir    = "D:\\Development\\School\\Types and Semantic\\Types-and-semantics\\base\\.cabal-sandbox\\i386-windows-ghc-7.8.3\\FunFlow-0.2.0.0"
libexecdir = "D:\\Development\\School\\Types and Semantic\\Types-and-semantics\\base\\.cabal-sandbox\\FunFlow-0.2.0.0"
sysconfdir = "D:\\Development\\School\\Types and Semantic\\Types-and-semantics\\base\\.cabal-sandbox\\etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "FunFlow_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "FunFlow_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "FunFlow_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "FunFlow_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "FunFlow_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
