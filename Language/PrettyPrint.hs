{-# LANGUAGE TypeSynonymInstances, FlexibleInstances  #-}
module Language.PrettyPrint where
import Language.Syntax
import Text.PrettyPrint
import Text.Parsec.Pos
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)

class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp String where
  disp  = text

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x
   else disp x

instance Disp PreTerm where
  disp (PVar x) = text x
  disp (Forall x p) = text "forall" <+> text x <+> text "." <+> disp p
  disp (a@(Imply p1 p2)) = dParen (precedence a) p1 <+> text "->" <+> dParen (precedence a -1) p2
  disp (Iota x p) = text "iota" <+> text x <+> text "." <+> disp p
  disp (a@(In t s)) = disp t <+> text "::" <+> dParen (precedence a - 1) s
  disp (s@(SApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(TApp s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (s@(App s1 s2)) = dParen (precedence s - 1) s1 <+> dParen (precedence s) s2
  disp (Lambda x t) = text "\\" <+> text x <+> text "." <+> disp t

  precedence (PVar _) = 12
  precedence (TApp _ _) = 10
  precedence (SApp _ _) = 10
  precedence (App _ _) = 10
  precedence (In _ _) = 10
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

instance Disp Proof where
  disp (Assume x) = brackets $ text x
  disp (PrVar x) = text x
  disp (a@(MP p1 p2)) = text "mp" <+> dParen (precedence a) p1 <+> dParen (precedence a) p2
  disp (a@(Inst p1 t)) = text "inst" <+> dParen (precedence a) p1 <+> disp t
  disp (a@(UG x p1)) = text "ug" <+> text x <+> dParen (precedence a) p1 
  disp (a@(Cmp p1)) = text "cmp" <+> dParen (precedence a) p1
  disp (a@(Beta p1)) = text "beta" <+> dParen (precedence a) p1
  disp (a@(Discharge x p1)) = text "discharge" <+> text x <+> dParen (precedence a) p1 
  disp (a@(InvCmp p1 f)) = text "invcmp" <+> dParen (precedence a) p1 <+> text ":" <+> disp f
  disp (a@(InvBeta p1 f)) = text "invbeta" <+> dParen (precedence a) p1 <+> text ":" <+> disp f
  precedence (PrVar _) = 12
  precedence _ = 4


