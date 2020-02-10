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

-- Inner 
newtype HOLIdent = HOLIdent Ident 
newtype HOLTerm  = HOLTerm Term 
newtype HOLPrimType = HOLPrimType PrimType
newtype HOLType  = HOLType Type 
newtype HOLConst = HOLConst Const 
newtype HOLArity = HOLArity Arity 

instance Pretty HOLIdent where 
    pretty (HOLIdent ident) = case ident of 
        Id id            -> string id
        Wildcard         -> string "_"
        TypedIdent id ty -> pretty id <+> string "::" <+> pretty ty

instance Pretty HOLConst where 
    pretty (HOLConst c) = case c of 
        TrueC  -> string "True"
        FalseC -> string "False"
        IntLiteral    i -> integer i
        CharLiteral   c -> string $ printf "CHR %#02x" $ ord c
        StringLiteral s | '\'' `elem` s -> string $ "[" ++ intercalate "," (map repr s) ++ "]"
                | otherwise     -> string $ "''" ++ s ++ "''"
                    where repr = printf "CHR %#02x" . ord
        Top    -> string "\\<top>"
        Bottom -> string "\\<bottom>"

instance Pretty HOLArity where 
    pretty (HOLArity (Arity Nothing n)) = string n
    pretty (HOLArity (Arity (Just ns) n)) = parens (sep $ punctuate comma $ map string ns) <+> string n

instance Pretty HOLTerm where 
    pretty = prettyHOLTerm 0

termAppPrecHOL = 100

prettyHOLTerm :: Precedence -> HOLTerm -> Doc
prettyHOLTerm p (HOLTerm t) = case t of
  TermIdent i           -> pretty $ HOLIdent i
  -- highest precedence and left associative
  TermApp t t'          -> prettyParen (p > termAppPrecHOL) $ prettyHOLTerm termAppPrecHOL t <+>
                             prettyHOLTerm (termAppPrecHOL+1) t'
  TermWithType t typ    -> prettyParen True $ pretty t <+> string "::" <+> pretty typ
  QuantifiedTerm q is t -> prettyQuantifier p q is t
  TermBinOp b t t'      -> (case b of
                              MetaImp -> prettyMetaImp p t t'
                              _       -> prettyBinOpTerm p b t t')
  TermUnOp u t          -> prettyUnOpTerm p u t
  ListTerm l ts r       -> pretty l <> hcat (intersperse (string ", ") (map (prettyHOLTerm termAppPrecHOL) ts)) <> pretty r
  ConstTerm const       -> pretty const
  AntiTerm str          -> pretty str  -- FIXME: zilinc
  CaseOf e alts         -> parens (string "case" <+> pretty e <+> string "of" <$> sep (punctuate (text "|") (map (prettyAssis "\\<Rightarrow>") alts)))
  RecordUpd upds        -> string "\\<lparr>" <+> sep (punctuate (text ",") (map (prettyAssis ":=") upds)) <+> string "\\<rparr>"
  RecordDcl dcls        -> string "\\<lparr>" <+> sep (punctuate (text ",") (map (prettyAssis "=") dcls)) <+> string "\\<rparr>"
  IfThenElse cond c1 c2 -> parens (string "if" <+> prettyHOLTerm p cond <+> string "then" <+> prettyHOLTerm p c1 <+> string "else" <+> prettyHOLTerm p c2)
  DoBlock dos           -> string "do" <$> sep (punctuate (text ";") (map pretty dos)) <$> string "od"
  DoItem  a b           -> pretty a <+> string "\\<leftarrow>" <+> pretty b 
  Set st                -> string "{" <> (case st of 
                              Quant q c -> pretty q <> string "." <+> pretty c
                              Range a b -> pretty a <> string ".." <> pretty b 
                              Listing lst -> sep (punctuate (text ",") (map pretty lst))) <> string "}"
  LetIn lt i            -> string "let" <+> sep (punctuate (text ";") (map (prettyAssis "=") lt)) <+> string "in" <+> pretty i

instance Pretty HOLType where
  pretty = prettyHOLType 0



-- Outer 
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
newtype HOLSig types = HOLSig (Sig types)
newtype HOLAbbrev types terms = HOLAbbrev (Abbrev types terms)
newtype HOLTheoryImports = HOLTheoryImports TheoryImports

instance (Pretty terms, Pretty types) =>  Pretty (HOLTheory terms types) where
  pretty (HOLTheory (Theory terms types)) = (pretty (thyImports thy) <$$>
                                             string "val _ = new_theory\"" <> string (thyName thy) <> string ) <$$>
                                             prettyThyDecls (thyBody thy) <>
                                             string "val _ = export_theory ()"
                                              <$$> empty

prettyHOLThyDecls :: (Pretty terms, Pretty types) => [HOLTheoryDecl types terms] -> Doc
prettyHOLThyDecls [] = empty
prettyHOLThyDecls (HOLTheoryDecl thyDecls) = (vsepPad . map pretty $ thyDecls) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLTheoryDecl types terms) where
  pretty (HOLTheoryDecl d)  = case d of
    Definition def      -> pretty $ HOLDef def
    OverloadedDef def sig -> prettyOvHOL def sig
    Abbreviation abbrev -> pretty $ HOLAbbrev abbrev
    ContextDecl c       -> pretty $ HOLContext c
    LemmaDecl d'        -> pretty d'
    LemmasDecl ld       -> pretty ld
    TypeSynonym ts      -> pretty ts
    TypeDeclDecl td     -> pretty td
    ConstsDecl c        -> pretty c
    RecordDecl fs       -> pretty fs
    DataTypeDecl dt     -> pretty dt
    FunFunction ff f    -> (if ff then string "fun" else string "function") <+> pretty f
    TheoryString s      -> string s
    PrimRec pr          -> pretty pr
    Declare dc          -> pretty dc

instance (Pretty terms, Pretty types) => Pretty (HOLContext types terms) where
  pretty (HOLContext (Context name cDecls)) = string "context" <+> string name <+> string "begin" <$$> 
                                 prettyThyDecls cDecls <> string "end" <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLDcl types terms) where
  pretty (HOLDcl (Dcl dclName dclRules)) = if (elem "simp" dclRules) 
    then string "export_rewrites \"" <> pretty dclName <> string "_def\""
    else empty

instance (Pretty terms, Pretty types) => Pretty (HOLPrc types terms) where
  pretty (HOLPrc (Prc thmDecl recCases)) =  string "primrec" <+> 
    pretty thmDecl <$$> string "where" <$$> sep (punctuate (text "|") (map prettyRecHOL recCases))

prettyRecHOL :: (Pretty terms) => (terms, terms) -> Doc
prettyRecHOL (p, e) = quote (pretty p <+> pretty "=" <+> pretty e)

instance (Pretty terms, Pretty types) => Pretty (HOLLemma types terms) where
  pretty (HOLLemma (Lemma schematic thmDecl props proof)) = string "Theorem" <+>
    pretty thmDecl <> string ":" <$$> indent 2 (vsep (map (quote . pretty) props)) <$$> indent 2 (pretty proof)
    <$$> empty

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLLemmas types terms) where
  pretty (HOLLemmas (Lemmas name lems)) = string "Theorem" <+>
    pretty name <+> string "=" <$$> indent 2 (vsep $ map pretty lems) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLTypeSyn types terms) where
  pretty (HOLTypeSyn (TypeSyn mbName typs tvs)) = string "Type" <+>
    prettyTypeVars (map TyVar tvs) <+>
    pretty mbName <+> string "=" <+> pretty typs <> string ";" <$$> empty

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLTypeDecl types terms) where
  pretty (HOLTypeDecl (TypeDecl tdName tvs)) = string "typedecl" <+>
    prettyTypeVars (map TyVar tvs) <+> pretty tdName

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLConsts types terms) where
  pretty (HOLConsts (Consts sig)) = string "consts" <+> pretty sig 

-- record type
-- CHECK: add semi-colons inbetween 
instance (Pretty terms, Pretty types) => Pretty (HOLRecord types terms) where
  pretty (HOLRecord (Record rName rFields tvs)) = string "Datatype:" <$$>
    -- prettyTypeVars (map TyVar tvs) <+>
    pretty rName <+> string "= <|" <$$> 
    (vsep (map (\rf -> let RecField n t = rf in indent 2 (pretty n <+> string ":" <+> pretty t)) rFields))
    <$$> string "|>" <$$> string "End" <$$> empty

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLDTCons types terms) where
  pretty (HOLDTCons (DTCons cn ts)) = pretty cn <+> (hsep . map (quote . pretty) $ ts)

instance (Pretty terms, Pretty types) => Pretty (HOLDatatype types terms) where
  pretty (HOLDatatype (Datatype dtName dtCons tvs)) = string "Datatype" <+>
    prettyTypeVars (map TyVar tvs) <+>
    pretty dtName <+> string "=" <$$> (vsep $ punctuate (char '|') $ map (indent 2 . pretty) dtCons) 
    <$$> string "End" <$$> Empty

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLClass types terms) where
  pretty (HOLClass (Class spec body)) = string "class" <+> pretty spec
                               <$> string "begin" 
                               <$> prettyThyDecls body <> string "end" <$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLClassSpec types terms) where
  pretty (HOLClassSpec ClassSpec) = error "TODO: instance Pretty (ClassSpec types terms)"  -- TODO: zilinc

-- CHECK
instance (Pretty terms, Pretty types) => Pretty (HOLInstantiation types terms) where
  pretty (HOLInstantiation (Instantiation names arity body)) = 
    string "instantiation" <+> sep (punctuate (string "and") (map pretty names))
    <+> string "::" <+> pretty arity
    <$> string "begin" 
    <$> prettyThyDecls body <> string "end" <$> empty

---- CHECK everything below ----
instance (Pretty terms, Pretty types) => Pretty (HOLInstance types terms) where
  pretty (HOLInstance head body) = 
    string "instance" <+> pretty head
    <$> prettyThyDecls body

instance Pretty HOLInstanceHead where
  pretty (HOLInstanceHead InstanceHeadNo) = empty
  pretty (HOLInstanceHead (InstanceHeadTh names arity)) = 
    sep (punctuate (string "and") (map pretty names)) <+> string "::" <+> pretty arity
  pretty (HOLInstanceHead (InstanceHeadIn name rel super)) =
    pretty name <+> pretty rel <+> pretty super

instance Pretty HOLClassRel where
  pretty (HOLClassRel ClassLessThan) = string "<"
  pretty (HOLClassRel ClassSubsetOf) = string "⊆"  -- FIXME: zilinc

instance (Pretty types, Pretty terms) => Pretty (HOLFunFunc types terms) where
  pretty (HOLFunFunc (FunFunc sig bd)) = (encloseSep empty empty (string "and" <> space) (map pretty sig)) -- FIXME: `and' on a new line / zilinc
                            <+> string "where"
                            <$$> align (pretty bd)

instance (Pretty types, Pretty terms) => Pretty (HOLEquations types terms) where
  pretty (HOLEquations (Equations terms)) = vsep $ punctuate (space <> string "|") $ map (dquotes . pretty) terms

instance Pretty HOLTheoremDecl where
  pretty (HOLTheoremDecl (TheoremDecl mbName attributes))
    | Nothing <- mbName, null attributes =
        error "In TheoremDecl, name == Nothing and attributes == [] is not allowed"
    | otherwise = maybe empty string mbName <> pattrs
       where pattrs = case attributes of
                  [] -> empty
                  attrs -> brackets . sep . punctuate comma $ map pretty attrs

instance Pretty HOLAttribute where
  pretty (HOLAttribute (Attribute n []))   = string n
  pretty (HOLAttribute (Attribute n args)) = string n <+> (hsep . map string $ args)

instance Pretty HOLProof where
  pretty (HOLProof (Proof methods proofEnd)) =
    (vsep . map (\m -> string "apply" <+> pretty m) $ methods) <$$> pretty proofEnd

instance Pretty HOLProofEnd where
  pretty (HOLProofEnd e) = string $ case e of
    ProofDone  -> "done"
    ProofSorry -> "sorry"

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
  pretty (HOLDef def) = string "definition" <> mbSig <$$> indent 2 (quote (pretty (defTerm def)))
    where mbSig = case defSig def of 
                    Just sig -> empty <$$> indent 2 (pretty sig) <$$> string "where" 
                    Nothing  -> empty

prettyOvHOL specDef sig = string "overloading" <> mbSig
                  <$$> string "begin"
                  <$$> indent 2 mbDefn
                  <$$> string "end"
    where mbSig = case defSig specDef of 
                    Just specSig ->
                      empty
                        <$$> indent 2 (pretty specSig)
                          <> string " \\<equiv> "
                          <> pretty sig
                    _ -> empty
          mbDefn =
            case defSig specDef of 
              Just specSig ->
                string "definition " <> pretty specSig <> string ": " <> quote (pretty (defTerm specDef))
              _ -> empty

instance Pretty types => Pretty (HOLSig types) where
  pretty (HOLSig d) = string (sigName d) <> mbTyp
    where mbTyp = case sigType d of
                    Just typ -> empty <+> string "::" <+> quote (pretty typ)
                    Nothing  -> empty

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
