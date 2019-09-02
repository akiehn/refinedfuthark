{-# OPTIONS_GHC -fno-warn-orphans #-}
module RefinedFuthark.Pretty (prettyFuthark) where

import RefinedFuthark.Syntax

import Text.PrettyPrint.Mainland.Class
import Text.PrettyPrint.Mainland


prettyFuthark :: Program -> String
prettyFuthark decs = pretty 80 (stack $ map ppr decs)

instance Pretty Dec where
  ppr (ValDec ident tps ps rt e) =
    text "let"
    <+> text ident
    <+> (spread $ map ppr tps)
    <+> spread (map (parens . ppr) ps)
    <+> text ":" <+> ppr rt
    <+> equals </>
    indent 2 (text "unsafe" <+> ppr e)
  ppr (ImportDec m) = text "import" <+> dquotes (text m)

instance Pretty TypeExp where
  ppr (ArrayType s t) = brackets (ppr s) <> ppr t
  ppr (TupleType _) = undefined
  ppr (TypeName n) = text n
  ppr (IntPredType _ _) = undefined
  ppr (BoolType _) = undefined
  ppr PlainInt = undefined
  ppr (IntType i) = text "i32" <> parens (ppr i)
  ppr (FunType t1 t2) = ppr t1 <+> text "->" <+> ppr t2
  ppr (PiType _ _ _) = undefined
  ppr (SigType _ _ _) = undefined
  ppr (UTVar _) = undefined
  ppr (ETVar _) = undefined
  ppr (GuardedType _ _) = undefined
  ppr (AssertingType _ _) = undefined
  ppr (PolyType _ _) = undefined

instance Pretty Exp where
  ppr (Var ident) = text ident
  ppr (UnOp _ _) = undefined
  ppr (IfThenElse _ _ _) = undefined
  ppr (Apply e1 s) = ppr e1 <+> spread (map ppr s)
  ppr (OpSection _) = undefined
  ppr (Lambda (ident, Just ta) (Just rt) e) = text "\\" <> parens (text ident <+> text ":" <+> ppr ta) <+> text ":" <+> ppr rt <+> text "->" <+> ppr e
  ppr (Lambda (ident, Nothing) Nothing e) = parens $ text "\\" <> text ident <+> text "->" <+> ppr e
  ppr (Index ident e) = ppr ident <> brackets (ppr e)
  ppr (FloatLit _) = undefined
  ppr (IntLit n) = ppr n
  ppr (BinOp _ _ _) = undefined
  ppr (Let lets e) = stack (map ppLet lets) </> text "in" <+> ppr e

ppLet :: (Ident, Maybe TypeExp, Exp) -> Doc
ppLet (ident, Nothing, e) = text "let" <+> text ident <+> equals <+> ppr e -- align (ppr exp1) <+> text "in" </> ppr exp2

instance Pretty TypeParam where
  ppr (SizeVar x) = brackets (text x)
  ppr (TypeVar x) = text "'" <> text x

instance Pretty Param where
  ppr (Param ident tp) = text ident <+> text ":" <+> ppr tp

instance Pretty IntIndex where
  ppr (IndexConst c) = ppr c
  ppr (IndexVar v) = ppr v
  ppr (ExIVar _) = undefined