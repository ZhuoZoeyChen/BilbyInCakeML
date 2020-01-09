module PrettyPrint where

-- Isabelle parser imports
import Isabelle.InnerAST 
import Isabelle.OuterAST
import Isabelle.PrettyHelper 
import Isabelle.Parser

import ASTTranslator 

prettify :: (L TheoryH) -> String
prettify theory = nm
    where 
        nm = thyNameH theory
