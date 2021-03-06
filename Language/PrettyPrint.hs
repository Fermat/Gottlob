{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Language.PrettyPrint where
import Language.Syntax
import Language.TypeInference
import Text.PrettyPrint
import Text.Parsec.Pos
import Data.Char
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)

class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp String where
  disp x = if (isUpper $ head x) || (isLower $ head x)
           then text x
           else if head x == '`'
                then text x
                else parens $ text x

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x 
   else disp x


instance Disp PreTerm where
  disp (PVar x) = disp x
  disp (Forall x p) = text "forall" <+> text x <+> text "." <+> disp p
  disp (a@(Imply p1 p2)) = dParen (precedence a) p1 <+> text "->"
                           <+> dParen (precedence a -1) p2
  disp (Iota x p) = text "iota" <+> text x <+> text "." <+> disp p
  disp (a@(In t s)) = disp t <+> text "::" <+> dParen (precedence a - 1) s
  disp (s@(SApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(TApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(App s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (Lambda x t) = text "\\" <+> text x <+> text "." <+> disp t
  disp (a@(MP p1 p2)) = text "mp" <+> dParen (precedence a) p1 <+> text "by" <+> dParen (precedence a) p2
  disp (a@(Inst p1 t)) = text "inst" <+> dParen (precedence a) p1 <+> text "by" <+> disp t
  disp (a@(UG x p1)) = text "ug" <+> text x <+> text "." <+> dParen (precedence a) p1 
  disp (a@(Cmp p1)) = text "cmp" <+> dParen (precedence a) p1
  disp (a@(SimpCmp p1)) = text "simpCmp" <+> dParen (precedence a) p1
  disp (a@(InvSimp p1 f)) = text "invsimp" <+> dParen (precedence a) p1 <+> text "from" <+> disp f
  disp (a@(Beta p1)) = text "beta" <+> dParen (precedence a) p1
  disp (a@(Discharge x Nothing p1)) = text "discharge" <+> text x <+> text "." <+> dParen (precedence a) p1
  disp (a@(Discharge x (Just t) p1)) = text "discharge" <+> text x <+> text ":" <+> disp t <+> text "." <+> dParen (precedence a) p1 
  disp (a@(InvCmp p1 f)) = text "invcmp" <+> dParen (precedence a) p1 <+> text "from" <+> disp f
  disp (a@(InvBeta p1 f)) = text "invbeta" <+> dParen (precedence a) p1 <+> text "from" <+> disp f

  disp (Pos _ t) = disp t
  precedence (Pos _ t) = precedence t
  precedence (PVar _) = 12
  precedence (TApp _ _) = 10
  precedence (SApp _ _) = 10
  precedence (App _ _) = 10
  precedence (In _ _) = 7
  precedence (Forall _ _) = 4
  precedence (Imply _ _) = 4
  precedence _ = 0
                          
instance Disp EType where
  disp Ind = text "i"
  disp Form = text "o"
  disp (a@(To e1 e2)) = dParen (precedence a) e1 <+> text "->" <+> dParen (precedence a -1) e2
  disp (EVar x) = text x
  precedence (To _ _) = 4
  precedence _ = 12

instance Disp Prog where
  disp (Name x) = disp x
  disp (Abs [] p) = disp p
  disp (Abs xs p) = text "\\" <+> (hsep $ map disp xs) <+> text "." <+> disp p
  disp (s@(Applica s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(AppPre s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (Match p alts) = text "case" <+> disp p <+> text "of" $$
                        nest 2 (vcat (map dAlt alts))
    where dAlt (c, args, p) =
            fsep [disp c <+> hsep (map disp args) <+> text "->", nest 2 $ disp p]
  disp (Let ls p) = text "let" $$ nest 2 (vcat ( map dDefs ls)) <+> text "in" $$  disp p
    where dDefs (v, t) = fsep [text v <+> text "=", nest 2 $ disp t]
  disp (TForall x p) = text "forall" <+> text x <+> text "." <+> disp p
  disp (a@(TImply p1 p2)) = dParen (precedence a) p1 <+> text "->"
                           <+> dParen (precedence a -1) p2
  disp (TIota x p) = text "iota" <+> text x <+> text "." <+> disp p
  disp (a@(TIn t s)) = disp t <+> text "::" <+> dParen (precedence a - 1) s
  disp (s@(TSApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(TSTApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (ProgPos p pr) = disp pr
  disp (a@(TMP p1 p2)) = text "mp" <+> dParen (precedence a) p1 <+> text "by" <+> dParen (precedence a) p2
  disp (a@(TInst p1 t)) = text "inst" <+> dParen (precedence a) p1 <+> text "by" <+> disp t
  disp (a@(TUG x p1)) = text "ug" <+> text x <+> text "." <+> dParen (precedence a) p1 
  disp (a@(TCmp p1)) = text "cmp" <+> dParen (precedence a) p1
  disp (a@(TBeta p1)) = text "beta" <+> dParen (precedence a) p1
  disp (a@(TDischarge x Nothing p1)) = text "discharge" <+> text x <+> text "." <+> dParen (precedence a) p1
  disp (a@(TDischarge x (Just t) p1)) = text "discharge" <+> text x <+> text ":" <+> disp t <+> text "." <+> dParen (precedence a) p1 
  disp (a@(TInvCmp p1 f)) = text "invcmp" <+> dParen (precedence a) p1 <+> text "from" <+> disp f
  disp (a@(TInvBeta p1 f)) = text "invbeta" <+> dParen (precedence a) p1 <+> text "from" <+> disp f
  disp (a@(If c p1 p2)) = text "if" <+> disp c <+> text "then" <+> disp p1 <+> text "else" <+> disp p2
  disp (a@(TSimpCmp p1)) = text "simpCmp" <+> dParen (precedence a) p1
  disp (a@(TInvSimp p1 f)) = text "invsimp" <+> dParen (precedence a) p1 <+> text "from" <+> disp f
  -- disp (s@(TPApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  -- disp (s@(TPFApp s1 s2)) = dParen (precedence s - 1) s1 <+> text "$" <+> dParen (precedence s) s2
  -- disp (TPLam x p) = text "\\" <+> disp x <+> text "." <+> disp p
  
  precedence (ProgPos _ pr) = precedence pr
  precedence (Name _) = 12
  precedence (Applica _ _) = 8
  precedence (AppPre _ _) = 8
  precedence (TSApp _ _) = 8
  precedence (TSTApp _ _) = 8
--  precedence (AppProof _ _) = 8
  -- precedence (TPApp _ _) = 8
  -- precedence (TPFApp _ _) = 7
  precedence _ = 0

instance Disp TScheme where
  disp (Scheme xs t) = if null xs then disp t
                         else text "forall" <+> (hsep $ map disp xs) <+>text "."<+>disp t

instance Disp (VName, TScheme) where
  disp (v, sc) = disp v <+> text "::" <+> disp sc

instance Disp (VName, FType) where
  disp (v, sc) = disp v <+> text "mapsto" <+> disp sc

instance Disp Args where
  disp (ArgProg p) = disp p
  disp (ArgType t) = disp t
  precedence (ArgType t) = precedence t
  precedence (ArgProg t) = precedence t

instance Disp FType where
  disp (FVar x) = text x
  disp (a@(FCons c args)) =
    text c <+> hsep (map (dParen (precedence a - 1)) args) 
  disp (a@(Arrow t1 t2)) = dParen (precedence a) t1 <+> text "->"
                           <+> dParen (precedence a - 1) t2
  disp (a@(Pi x t1 t2)) = parens (text x <+> text "::"<+> disp t1) <+>
                      text "->" <+> dParen (precedence a - 1) t2
  disp (FTPos p pr) = disp pr
  precedence (FTPos _ pr) = precedence pr
  precedence (FCons _ _) = 10
  precedence (FVar _) = 12
  precedence (Arrow _ _) = 4
  precedence (Pi _ _ _) = 4

instance Disp Datatype where
  disp d1@(Data d params cons) = -- disp $ show d1
    hang (text "data" <+> text d <+> hsep (map text params)
          <+> text "where") 2 (vcat (map dispCon cons))
   where dispCon (n, t) = disp n <+> text "::" <+> disp t
    
instance Disp Module where
  disp (Module name decl) = text "module" <+> text name $$ vcat (map disp decl)

instance Disp Decl where
  disp (ProgDecl x p) = disp x <+> text "=" <+>disp p
  disp (ProofDecl x m ps f) =
    text "theorem" <+> text x <+>
    (case m of
          Just m' -> text "[" <> disp m' <> text "]"
          Nothing -> text "")<+>text "." <+> disp f $$
    text "proof" $$ nest 2 (vcat (map dispPs ps))
                            $$ text "qed"
    where dispPs (n, Left a, Just f) = text "[" <> text n <> text "]" <+> text ":" <+> disp f
          dispPs (n, Right p, Just f) = text n <+> text "=" <+> disp p <+> text ":" <+> disp f
          dispPs (n, Right p, Nothing) = text n <+> text "=" <+> disp p 
  disp (DataDecl p d False) = disp d
  disp (DataDecl p d True) = disp d $$ nest 2 (text "deriving" <+> text "Ind")
  disp (SetDecl x s) = disp x <+> text "=" <+> disp s
  disp (TacDecl x args (Left s)) = text "tactic" <+> disp x <+>(hsep $ map text args) <+> text "=" <+> disp s
  disp (TacDecl x args (Right ps)) = text "tactic" <+> disp x <+>(hsep $ map text args) <+> text "=" $$ nest 2 (vcat (map dispPs ps))
    where dispPs (n, Left a, Just f) = text "[" <> text n <> text "]" <+> text ":" <+> disp f
          dispPs (n, Right p, Just f) = text n <+> text "=" <+> disp p <+> text ":" <+> disp f
          dispPs (n, Right p, Nothing) = text n <+> text "=" <+> disp p 
  disp (FormOperatorDecl s1 i s2) = text "formula" <+> text s1 <+>
                                    disp i <+> disp s2
  disp (ProgOperatorDecl s1 i s2) = text "prog" <+> text s1 <+>
                                    disp i <+> disp s2
  disp (ProofOperatorDecl s1 i s2) = text "proof" <+> text s1 <+>
                                    disp i <+> disp s2
  disp (PatternDecl x pats prog) = disp x <+> hsep (map helper pats) <+> text "=" <+> disp prog
    where helper (Name x) = disp x
          helper a = parens $ disp a
  -- disp (SpecialOperatorDecl s1 i s2) = text "special" <+> text s1 <+>
  --                                   disp i <+> disp s2

instance Disp Constraints where
  disp l = vcat $ map dispPair l
    where dispPair (t1,t2) = disp t1 <+> text "=" <+> disp t2

instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp)
             <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = (disp (errorPos pe)) $$
           (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)


test = disp (Pi "n" (FVar "Nat") (Arrow (FVar "U") (Arrow (FCons "Vec" [ArgType (FVar "U"),ArgProg (Name "n")]) (FCons "Vec" [ArgType (FVar "U"),ArgProg (Applica (Name "s") (Name "n"))]))))
test1 = disp (Data "Nat" [] [("z",FVar "Nat"),("s",Arrow (FVar "Nat") (FVar "Nat"))])
