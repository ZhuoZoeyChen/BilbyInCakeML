module Main where

-- system imports
import System.Environment
import System.Exit
import Text.Printf
import Text.Parsec
import Text.Parsec.String
import Text.PrettyPrint.ANSI.Leijen
import Data.Data
import System.IO

import Isabelle.InnerAST 
import Isabelle.OuterAST
import Isabelle.PrettyHelper 
import Isabelle.Parser

import ASTTranslator
import PrettyPrint
import PrettyWrapper

getFile :: IO (Maybe String)
getFile = do
  args <- getArgs
  return $ case args of 
             []     -> Nothing
             file:_ -> Just file

exitOnNothing :: String -> IO (Maybe a) -> IO a
exitOnNothing errorString io = do
  mb <- io
  case mb of
    Nothing -> putStrLn errorString >> exitWith (ExitFailure 1)
    Just x  -> return x
  
-- moveComments ::
-- moveComments file = undefined

main :: IO ()
main = do 
    file <- exitOnNothing "You must provide a file name as first argument" getFile
     -- nfile <- moveComments file
    eRes <- parseFromFile topLevelL file
    case eRes of
        Left err  -> printf "Error parsing %s\n%s\n" file (show err)
        Right res -> do 
            ho4 <- return(translate res) 
            pho4 <- return(prettify ho4)
            -- writeFile "/home/zoey/BilbyInCakeML/AfsSD" (show res)

            handle <- openFile "AfsSDParsed.sml" WriteMode
            hPutDoc handle (pretty (convert res))
            hClose handle

