
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

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

data TheoryH types terms = TheoryH { thyNameH :: String, thyImportsH :: TheoryImports} 
                        deriving (Data, Typeable, Show)
                        --, thyBodyH :: ?

theoryH :: Theory types terms -> TheoryH types terms
theoryH theory = TheoryH { thyNameH = thyName theory, thyImportsH = thyImports theory}
--, thyBodyH = ? 
-- translateDecl :: TheoryDecl types terms -> ?

translate :: (L Theory) -> (L TheoryH)
translate (Theory n ip bd) = TheoryH { thyNameH = n, thyImportsH = ip}
--, thyBodyH = map translateDecl bd 


