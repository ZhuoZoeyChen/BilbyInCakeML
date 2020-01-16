module PrettyPrint where

-- Isabelle parser imports
import Isabelle.InnerAST 
import Isabelle.OuterAST
import Isabelle.PrettyHelper 
import Isabelle.Parser

import ASTTranslator 

prettify :: (L TheoryH) -> String
prettify theory = "TODO: open sometheories\n\n" ++ "val _ = new_theory \""++nm++"\"\n\n" ++ "val _ = export_theory ()"
    where 
        nm = thyNameH theory
