module Printer where

import ASTTranslator
import PrettyPrint

main :: IO ()
main = do 
    file <- exitOnNothing "You must provide a file name as first argument" getFile
    eRes <- parseFromFile topLevelL file
  case eRes of
    Left err  -> printf "Error parsing %s\n%s\n" path (show err)
    Right res -> do 
            ho4 <- translate res 
            pres <- prettify res
            print pres
