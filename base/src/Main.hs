-- (C) 2013-14 Pepijn Kokke & Wout Elsinghorst
-- Modifications made Jurriaan Hage

module Main
  ( module Ast
  , module Parsing 
  ) where

import Ast
import Parsing
import Algorithm
import qualified Data.Set as S
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
  --putStrLn $ show (fst $ adjustAnnotation (parseExpr content, S.empty))
  runAlgorithm $ parseExpr content

runAlgorithm :: Expr -> IO ()
runAlgorithm e =  do
            let (newExpr, annotation) = adjustAnnotation (e,S.empty)
            (ty,subst,constraint,vars,ann) <- w (M.empty, newExpr) (collectVarsExpr e) annotation
            putStrLn $ "Parsed code: " ++ show newExpr
            putStrLn $ "Type: " ++ (view ty)
            putStrLn $ "Constraint: " ++ (show constraint)
            putStrLn $ "Total annotation " ++ (show ann)