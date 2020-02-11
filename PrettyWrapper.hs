module PrettyWrapper 
where 

-- system imports 
import Text.Parsec.Expr (Assoc(..))
import Text.PrettyPrint.ANSI.Leijen 
import Prelude hiding ((<$>))
import Text.Printf (printf)
import Data.Char (ord)
import Data.List
import Data.Data
import Data.Typeable

-- Isabelle imports
import Isabelle.InnerAST
import Isabelle.OuterAST
import Isabelle.PrettyHelper

------------------------------------------------------------------------

---------------         Inner                ---------------------------

------------------------------------------------------------------------

newtype HOLIdent = HOLIdent Ident 
newtype HOLTerm  = HOLTerm Term 
newtype HOLPrimType = HOLPrimType PrimType
newtype HOLType  = HOLType Type 
newtype HOLConst = HOLConst Const 
newtype HOLArity = HOLArity Arity 

quantifierAuxHOL :: Quantifier -> QuantifierRec
quantifierAuxHOL q = case q of
  MetaBind    -> QuantifierRec 0  "/\\"
  Lambda      -> QuantifierRec 3  "\\"
  Forall      -> QuantifierRec 10 "!"
  Exists      -> QuantifierRec 10 "?"
  ExistsBang  -> QuantifierRec 10 "?!"

quantifierPrecHOL = quantifierRecPrecedence . quantifierAuxHOL
quantifierSymHOL =  quantifierRecSymbol . quantifierAuxHOL

instance Pretty HOLIdent where 
    pretty (HOLIdent ident) = case ident of 
        Id id            -> string id
        Wildcard         -> string "_"
        TypedIdent id ty -> pretty id <+> string "::" <+> pretty ty

instance Pretty HOLConst where 
    pretty (HOLConst c) = case c of 
        TrueC  -> string "T"
        FalseC -> string "F"
        IntLiteral    i -> pretty i
        CharLiteral   c -> pretty c
        StringLiteral s -> pretty s
        Top    -> string "\\<top>" --FIXME: zoeyc
        Bottom -> string "\\<bottom>" --FIXME: zoeyc

instance Pretty HOLArity where 
    pretty (HOLArity (Arity Nothing n)) = string n
    pretty (HOLArity (Arity (Just ns) n)) = parens (sep $ punctuate comma $ map string ns) <+> string n

instance Pretty HOLTerm where 
    pretty = prettyHOLTerm 0

termAppPrecHOL = 100

prettyHOLTerm :: Precedence -> HOLTerm -> Doc
prettyHOLTerm p (HOLTerm tm) = case tm of
  TermIdent i           -> pretty $ HOLIdent i
  -- highest precedence and left associative
  TermApp t t'          -> prettyParen (p > termAppPrecHOL) $ prettyHOLTerm termAppPrecHOL (HOLTerm t) <+>
                             prettyHOLTerm (termAppPrecHOL+1) (HOLTerm t')
  TermWithType t typ    -> prettyParen True $ pretty (HOLTerm t) <+> string "::" <+> pretty (HOLType typ)
  QuantifiedTerm q is t -> prettyQuantifierHOL p q is t
  TermBinOp b t t'      -> prettyBinOpTermHOL p b (HOLTerm t) (HOLTerm t')
  -- TermBinOp b t t'      -> (case b of
  --                             MetaImp -> prettyMetaImpHOL p t t'
  --                             _       -> prettyBinOpTermHOL p b t t')
  TermUnOp u t          -> prettyUnOpTerm p u (HOLTerm t)
  ListTerm l ts r       -> pretty l <> hcat (intersperse (string ", ") (map ((prettyHOLTerm termAppPrecHOL). HOLTerm) ts)) <> pretty r
  ConstTerm const       -> pretty const
  AntiTerm str          -> empty
  CaseOf e alts         -> parens (string "case" <+> pretty e <+> string "of" <$> sep (map ((text "|" <+> ). (prettyAssis "=>")) alts))
  RecordUpd upds        -> string "<|" <+> sep (punctuate (text ";") (map (prettyAssis ":=") upds)) <+> string "|>"
  RecordDcl dcls        -> string "<|" <+> sep (punctuate (text ";") (map (prettyAssis ":=") dcls)) <+> string "|>"
  IfThenElse cond c1 c2 -> parens (string "if" <+> prettyHOLTerm p cond <+> string "then" <+> prettyHOLTerm p c1 <+> string "else" <+> prettyHOLTerm p c2)
  DoBlock dos           -> string "do" <$> sep (punctuate (text ";") (map pretty dos)) <$> string "od"
  DoItem  a b           -> pretty a <+> string "\\<leftarrow>" <+> pretty b 
  Set st                -> string "{" <> (case st of 
                              Quant q c -> pretty q <> string "." <+> pretty c
                              Range a b -> pretty a <> string ".." <> pretty b 
                              Listing lst -> sep (punctuate (text ";") (map pretty lst))) <> string "}"
                          -- FIXME: zoeyc
  LetIn lt i            -> string "let" <+> sep (punctuate (text ";" <$>) (map (prettyAssis "=") lt)) <$$> string "in" <$$> pretty i
                          -- FIXME: make indentation better / zoeyc
prettyBinOpTermHOL :: Precedence -> TermBinOp -> HOLTerm -> HOLTerm -> Doc
prettyBinOpTermHOL p b = prettyBinOp p prettyHOLTerm (termBinOpRec b) prettyHOLTerm

prettyUnOpTermHOL :: Precedence -> TermUnOp -> HOLTerm -> Doc
prettyUnOpTermHOL p u = prettyUnOp p (termUnOpRec u) prettyHOLTerm

--
-- [| P_1; ...; P_n |] ==> Q is syntactic sugar for P_1 ==> ... ==> P_n ==> Q
--
-- @prettyMetaImp@ takes care of printing it that way.
-- prettyMetaImpHOL :: Precedence -> Term -> Term -> Doc
-- prettyMetaImpHOL p t t' = case t' of
--   t'@(TermBinOp MetaImp _ _) -> go [t] t'
--   _                   -> prettyBinOpTerm p MetaImp t t'
--   where
--     p' = termBinOpPrec MetaImp
--     go ts (TermBinOp MetaImp t t') = go (t:ts) t'
--     go ts t                    =
--       string "\\<lbrakk>" <>
--       (hsep . punctuate semi . map (prettyTerm (p'+1)) . reverse $ ts) <>
--       string "\\<rbrakk>" <+> string (termBinOpSym MetaImp) <+> prettyTerm p' t

prettyQuantifierHOL :: Precedence -> Quantifier -> [Term] -> Term -> Doc
prettyQuantifierHOL p q is t = prettyParen (p > quantifierPrec q) $ string (quantifierSym q) <>
                              (hsep . map (prettyHOLTerm 0. HOLTerm) $ is) <> char '.' <+> pretty (HOLTerm t)

instance Pretty HOLPrimType where
  pretty ty = string $ case ty of
    IntT  -> "int"
    BoolT -> "bool"
    NatT  -> "nat"

instance Pretty HOLType where
  pretty = prettyHOLType 0

tyArrowSymHOL = "\\<Rightarrow>" -- FIXME: zoeyc
tyTupleSymHOL = "\\<times>" -- FIXME: zoeyc

prettyTypeVarsHOL :: [HOLType] -> Doc
prettyTypeVarsHOL [] = empty
prettyTypeVarsHOL [ty] = prettyHOLType 100 ty -- application has highest precedence
prettyTypeVarsHOL tys = char '(' <> (hsep . punctuate (char ',') . map (prettyHOLType 0) $ tys) <> char ')'  -- FIXME: not very pretty / zilinc

prettyHOLType :: Precedence -> HOLType -> Doc
prettyHOLType p (HOLType ty) =
    case ty of
      TyVar v          -> char '\'' <> string v
      TyDatatype s tys -> prettyTypeVarsHOL (HOLType tys) <+> string s
      TyPrim t         -> pretty (HOLPrimType t)
      -- TyArrow is right associative
      TyArrow t t'     -> prettyParen (p > pa) $ prettyHOLType (pa+1) (HOLType t) <+>
                          string tyArrowSymHOL <+> prettyType pa (HOLType t')
      -- TyTuple is right associative
      TyTuple t t'     -> prettyParen (p > pt) $ prettyHOLType (pt+1) (HOLType t) <+>
                          string tyTupleSymHOL <+> prettyHOLType pt (HOLTtpe t')
      AntiType t       -> string t  -- FIXME: zilinc
  where
     pa = 1
     pt = 2


------------------------------------------------------------------------

---------------         Outer                ---------------------------

------------------------------------------------------------------------


newtype HOLTheory types terms = HOLTheory (Theory types terms)
newtype HOLTheoryDecl types terms = HOLTheoryDecl (TheoryDecl types terms)
newtype HOLContext types terms = HOLContext (Context types terms)
newtype HOLDcl types terms  = HOLDcl (Dcl types terms)
newtype HOLPrc types terms = HOLPrc (Prc types terms)
newtype HOLLemma types terms = HOLLemma (Lemma types terms)
newtype HOLLemmas types terms = HOLLemmas (Lemmas types terms)
newtype HOLTypeSyn types terms = HOLTypeSyn (TypeSyn types terms)
newtype HOLTypeDecl types terms = HOLTypeDecl (TypeDecl types terms)
newtype HOLConsts types terms = HOLConsts (Consts types terms)
newtype HOLRecord types terms = HOLRecord (Record types terms)
newtype HOLDTCons types terms = HOLDTCons (DTCons types terms)
newtype HOLDatatype types terms = HOLDatatype (Datatype types terms)
newtype HOLClass types terms = HOLClass (Class types terms)
newtype HOLClassSpec types terms = HOLClassSpec (ClassSpec types terms)
newtype HOLInstantiation types terms = HOLInstantiation (Instantiation types terms)
newtype HOLInstance types terms = HOLInstance (Instance types terms)
newtype HOLInstanceHead = HOLInstanceHead InstanceHead
newtype HOLClassRel = HOLClassRel ClassRel 
newtype HOLFunFunc types terms = HOLFunFunc (FunFunc types terms)
newtype HOLEquations types terms = HOLEquations (Equations types terms)
newtype HOLTheoremDecl = HOLTheoremDecl TheoremDecl 
newtype HOLAttribute = HOLAttribute Attribute
newtype HOLProof = HOLProof Proof 
newtype HOLProofEnd = HOLProofEnd ProofEnd
newtype HOLMethod = HOLMethod Method 
newtype HOLMethodModifier = HOLMethodModifier MethodModifier 
newtype HOLDef types terms = HOLDef (Def types terms)
-- newtype HOLSig types = HOLSig (Sig types)
newtype HOLAbbrev types terms = HOLAbbrev (Abbrev types terms)
newtype HOLTheoryImports = HOLTheoryImports TheoryImports

instance (Pretty terms, Pretty types) =>  Pretty (HOLTheory terms types) where
  pretty (HOLTheory thy) = (pretty (thyImports thy) <$$>
                                             string "val _ = new_theory\"" <> string (thyName thy) <> string ) <$$>
                                             prettyHOLThyDecls (HOLTheoryDecl (thyBody thy)) <>
                                             string "val _ = export_theory ()"
                                              <$$> empty

prettyHOLThyDecls :: (Pretty terms, Pretty types) => [HOLTheoryDecl types terms] -> Doc
prettyHOLThyDecls [] = empty
prettyHOLThyDecls thyDecls = (vsepPad . map pretty $ thyDecls) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLTheoryDecl types terms) where
  pretty (HOLTheoryDecl d)  = case d of
    Definition def        -> pretty $ HOLDef def
    OverloadedDef def sig -> empty
    Abbreviation abbrev   -> pretty $ HOLAbbrev abbrev
    ContextDecl c         -> pretty $ HOLContext c
    LemmaDecl d'          -> pretty d'
    LemmasDecl ld         -> pretty ld
    TypeSynonym ts        -> pretty ts
    TypeDeclDecl td       -> pretty td
    ConstsDecl c          -> pretty c
    RecordDecl fs         -> pretty fs
    DataTypeDecl dt       -> pretty dt
    FunFunction ff f      -> (if ff then string "fun" else string "function") <+> pretty f
    TheoryString s        -> string s
    PrimRec pr            -> pretty pr
    Declare dc            -> pretty dc
-- FIXME : zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLContext types terms) where
  pretty (HOLContext (Context name cDecls)) = string "context" <+> string name <+> string "begin" <$$> 
                                 prettyThyDecls cDecls <> string "end" <$$> empty -- FIXME : zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLDcl types terms) where
  pretty (HOLDcl (Dcl dclName dclRules)) = if (elem "simp" dclRules) 
    then string "export_rewrites \"" <> pretty dclName <> string "_def\""
    else empty

instance (Pretty terms, Pretty types) => Pretty (HOLPrc types terms) where
  pretty (HOLPrc (Prc thmDecl recCases)) =  string "Definition" <+> 
    pretty thmDecl <> string ":" <$$> vsep (punctuate (text "/\\") (map prettyRec (HOLTerm recCases))) 
    <$$> string "End" <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLLemma types terms) where
  pretty (HOLLemma (Lemma schematic thmDecl props proof)) = string "Theorem" <+>
    pretty thmDecl <> string ":" <$$> indent 2 (vsep (punctuate (text "/\\") (map (parens. pretty . HOLTerm) props))) 
    <$$> indent 2 (pretty proof) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLLemmas types terms) where
  pretty (HOLLemmas (Lemmas name lems)) = string "Theorem" <+>
    pretty name <+> string "=" <$$> indent 2 (vsep $ map pretty lems) <$$> empty --FIXME: zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLTypeSyn types terms) where
  pretty (HOLTypeSyn (TypeSyn mbName typs tvs)) = string "Type" <+>
    prettyTypeVars (map TyVar tvs) <+>
    pretty mbName <+> string "=" <+> pretty typs <> string ";" <$$> empty

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLTypeDecl types terms) where
  pretty (HOLTypeDecl (TypeDecl tdName tvs)) = string "Datatype:" <$$>
    prettyTypeVars (map TyVar tvs) <+> pretty tdName

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLConsts types terms) where
  pretty (HOLConsts (Consts sig)) = string "consts" <+> pretty sig 

instance (Pretty terms, Pretty types) => Pretty (HOLRecord types terms) where
  pretty (HOLRecord (Record rName rFields tvs)) = string "Datatype:" <$$>
    -- prettyTypeVars (map TyVar tvs) <+>
    pretty rName <+> string "= <|" <$$> 
    (vsep (punctuate (string ";") (map (\rf -> let RecField n t = rf in indent 2 (pretty n <+> string ":" <+> pretty t)) rFields)))
    <$$> string "|>" <$$> string "End" <$$> empty

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLDTCons types terms) where
  pretty (HOLDTCons (DTCons cn ts)) = pretty cn <+> (hsep . map (quote . pretty) $ ts)

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLDatatype types terms) where
  pretty (HOLDatatype (Datatype dtName dtCons tvs)) = string "Datatype:" <$$>
    prettyTypeVars (map TyVar tvs) <+>
    pretty dtName <+> string "=" <$$> (vsep $ punctuate (char '|') $ map (indent 2 . pretty) dtCons) 
    <$$> string "End" <$$> Empty

-- FIXME: HOL4 does not have such concept as a "class" / zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLClass types terms) where
  pretty (HOLClass (Class spec body)) = empty

instance (Pretty terms, Pretty types) => Pretty (HOLClassSpec types terms) where
  pretty (HOLClassSpec ClassSpec) = error "TODO: instance Pretty (ClassSpec types terms)"  -- TODO: zilinc

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLInstantiation types terms) where
  pretty (HOLInstantiation (Instantiation names arity body)) = emtpy
    -- string "instantiation" <+> sep (punctuate (string "and") (map pretty names))
    -- <+> string "::" <+> pretty arity
    -- <$> string "begin" 
    -- <$> prettyThyDecls body <> string "end" <$> empty

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLInstance types terms) where
  pretty (HOLInstance head body) = empty
    -- string "instance" <+> pretty head
    -- <$> prettyThyDecls body

-- FIXME: zoeyc
instance Pretty HOLInstanceHead where
  pretty h = empty
  -- pretty (HOLInstanceHead InstanceHeadNo) = empty
  -- pretty (HOLInstanceHead (InstanceHeadTh names arity)) = 
  --   sep (punctuate (string "and") (map pretty names)) <+> string "::" <+> pretty arity
  -- pretty (HOLInstanceHead (InstanceHeadIn name rel super)) =
  --   pretty name <+> pretty rel <+> pretty super

-- FIXME: zoeyc
instance Pretty HOLClassRel where
  pretty cr = empty
  -- pretty (HOLClassRel ClassLessThan) = string "<"
  -- pretty (HOLClassRel ClassSubsetOf) = string "⊆"  -- FIXME: zilinc

-- FIXME: zoeyc
instance (Pretty types, Pretty terms) => Pretty (HOLFunFunc types terms) where
  pretty (HOLFunFunc (FunFunc sig bd)) = string "Definition" <+>  (encloseSep empty empty (string "and" <> space) (map pretty sig)) -- FIXME: `and' on a new line / zilinc
                            <+> string "where"
                            <$$> align (pretty bd)

instance (Pretty types, Pretty terms) => Pretty (HOLEquations types terms) where
  pretty (HOLEquations (Equations terms)) = vsep $ punctuate (space <> string "/\\") $ map (bracketL. pretty. HOLTerms) terms

instance Pretty HOLTheoremDecl where
  pretty (HOLTheoremDecl (TheoremDecl mbName attributes))
    | Nothing <- mbName, null attributes =
        error "In TheoremDecl, name == Nothing and attributes == [] is not allowed"
    | otherwise = maybe empty string mbName <> pattrs
       where pattrs = if (elem "simp" attributes) 
                      then bracketL (string "simp")
                      else empty

instance Pretty HOLAttribute where
  pretty (HOLAttribute (Attribute lst))   = if (elem "simp" lst) 
    then bracketL (string "simp") 
    else empty

instance Pretty HOLProof where
  pretty (HOLProof (Proof methods proofEnd)) =
    (vsep (punctuate (string ">>") (map (\m -> string "APPLY_TAC" <+> bracketL (pretty (HOLMethod m))) methods))) 
    <$$> pretty proofEnd
-- FIXME: proof translation needed / zoeyc

instance Pretty HOLProofEnd where
  pretty (HOLProofEnd e) = (string end) <$$> string "QED" <$$> empty
    where end = case e of
                 ProofDone  -> emtpy
                 ProofSorry -> "cheat"

instance Pretty HOLMethod where
  pretty = prettyMethodTopLevelHOL 0

prettyMethodTopLevelHOL p (HOLMethod m) = case m of
  Method name []      -> string name
  MethodModified m mm -> (parens $ prettyMethodHOL p m) <> pretty mm
  _                   -> parens $ prettyMethodHOL p m

prettyMethodHOL :: Int -> HOLMethod -> Doc
prettyMethodHOL p (HOLMethod m) = case m of
    Method name args ->
      hsep . map string $ name:args
    MethodModified m' mm -> prettyMethodTopLevel p m' <> pretty mm
    MethodCompound binOp m' m'' -> 
      prettyBinOp p prettyMethodHOL (methodBinOpRec binOp) prettyMethod m' m''
    
instance Pretty HOLMethodModifier where
  pretty (HOLMethodModifier m) = case m of
    MMOptional  -> string "?"
    MMOneOrMore -> string "+"
    MMGoalRestriction mbI -> brackets $ maybe empty (string . show) $ mbI

instance (Pretty terms, Pretty types) => Pretty (HOLDef types terms) where
  pretty (HOLDef def) = string "Definition" <> mbSig <$$> indent 2 (pretty . HOLTerm (defTerm def)) <$$> string "End"
    where mbSig = case defSig def of 
                    Just sig -> (string (sigName sig)) <$$> string ":" 
                    Nothing  -> empty

-- FIXME: zoeyc
prettyOvHOL specDef sig = string "overloading" <> mbSig
                  <$$> string "begin"
                  <$$> indent 2 mbDefn
                  <$$> string "end"
    where mbSig = case defSig specDef of 
                    Just specSig ->
                      empty
                        <$$> indent 2 (pretty specSig)
                          <> string "="
                          <> pretty sig
                    _ -> empty
          mbDefn =
            case defSig specDef of 
              Just specSig ->
                string "definition " <> pretty specSig <> string ": " <> quote (pretty (defTerm specDef))
              _ -> empty

instance (Pretty terms, Pretty types) => Pretty (HOLAbbrev types terms) where
  pretty (HOLAbbrev a) = string "abbreviation" <+> mbSig <$$> (indent 2 (quote (pretty (abbrevTerm a))))
    where mbSig = case abbrevSig a of 
                    Just sig -> pretty sig <$$> string "where" 
                    Nothing  -> empty

instance Pretty HOLTheoryImports where
  pretty (HOLTheoryImports (TheoryImports is)) = string "open" <+> fillSep (map string is)

-- smart constructor

mkComment :: String -> TheoryDecl types terms
mkComment s = TheoryString $ "(* " ++ s ++ " *)"
