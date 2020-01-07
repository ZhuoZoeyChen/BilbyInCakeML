module ASTTranslator where

-- InnerAST system imports
import Data.Data
import Data.List
import Data.Typeable
import Text.Parsec.Expr (Assoc(..))
import Text.PrettyPrint.ANSI.Leijen
import Prelude hiding ((<$>))

-- Parser system imports
import Control.Applicative hiding (many)
import Control.Monad.Identity 
import Data.Char (isSpace)
--import Data.List
import Data.Monoid
import qualified Text.Parsec as P
import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr

-- Isabelle parser imports
import Isabelle.InnerAST 
import Isabelle.OuterAST
import Isabelle.PrettyHelper 
import Isabelle.Parser

nameH :: Name -> Name
nameH name = name

data TheoryH = TheoryH { thyNameH :: String } 
                        deriving (Show)
                        --Data, Typeable, 

theoryH :: Theory types terms -> TheoryH
theoryH theory = TheoryH { thyNameH = thyName theory}

translate :: (L Theory) -> TheoryH
translate (Theory n ip bd) = TheoryH { thyNameH = n }


