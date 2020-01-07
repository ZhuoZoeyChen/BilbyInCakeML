module ASTTranslator where

-- import Data.Data
-- import Data.List
-- -- import Data.Typeable
-- import Text.Parsec.Expr (Assoc(..))
-- import Text.PrettyPrint.ANSI.Leijen
-- #if __GLASGOW_HASKELL__ >= 709
-- import Prelude hiding ((<$>))
-- #endif

import Isabelle.InnerAST 
import Isabelle.OuterAST
import Isabelle.PrettyHelper 

import Isabelle.Parser

nameH :: Name -> Name
nameH name = name

data TheoryH = TheoryH { thyNameH :: String } 
                        deriving (Data, Typeable, Show)

theoryH :: Theory types terms -> TheoryH
theoryH theory = TheoryH { thyNameH = thyName theory}

translate :: Theory Type Term -> TheoryH
translate (Theory n ip bd) = TheoryH { thyNameH = n }


