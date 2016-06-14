-- (C) 2013-14 Pepijn Kokke & Wout Elsinghorst
-- Modifications made Jurriaan Hage

module Main
  ( module Ast
  , module Parsing 
  ) where

import Ast
import Parsing
import Algorithm
import Data.Set (Set)
import qualified Data.Map as M
import View
  
 
run :: String -> IO ()   
run name = do
  p <- parse name
  putStrLn (show p)
  return ()

-- |Parse and label program
parse :: String -> IO ()
parse programName = do
  let fileName = "../examples/" ++ programName++".fun"
  content <- readFile fileName
  putStrLn $ "Code: " ++ (show $ parseExpr content)
  runAlgorithm $ (parseExpr content)

runAlgorithm :: Expr -> IO ()
runAlgorithm e =  do
			(ty,subst,constraint,vars,ann) <- w (M.empty, e) (varsExpr e) (annotationExpr e)
			putStrLn $ "Type: " ++ (view ty)
			putStrLn $ "Constraint: " ++ (show constraint)
