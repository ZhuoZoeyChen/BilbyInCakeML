module PrettyPrint where

prettify :: TheoryH -> String
prettify theory = nm
    where 
        nm = thyNameH theory
