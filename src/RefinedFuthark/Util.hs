
module RefinedFuthark.Util where

import RefinedFuthark.Syntax
import GHC.Stack

replaceIVar :: Ident -> Ident -> TypeExp -> TypeExp
replaceIVar old new t = case t of
  PlainInt -> PlainInt
  ArrayType Nothing tp -> ArrayType Nothing (replaceIVar old new tp)
  ArrayType (Just idx) tp -> ArrayType (Just (replaceIndex old new idx)) (replaceIVar old new tp)
  TupleType tps -> TupleType $ map (replaceIVar old new) tps
  TypeName n -> TypeName n
  IntPredType _i _b -> undefined
  BoolType b -> BoolType (replaceBoolIndex old new b)
  IntType idx -> IntType (replaceIndex old new idx)
  FunType t1 t2 -> FunType (replaceIVar old new t1) (replaceIVar old new t2)
  PiType ident s tp -> PiType ident (replaceSort old new s) (replaceIVar old new tp)

replaceIndex :: Ident -> Ident -> IntIndex -> IntIndex
replaceIndex old new idx1 = case idx1 of
  IndexConst c -> IndexConst c
  IndexVar ident -> if ident == old then IndexVar new else IndexVar ident

replaceBoolIndex :: Ident -> Ident -> BoolIndex -> BoolIndex
replaceBoolIndex old new bi = case bi of
  ILess idx1 idx2 -> ILess (replaceIndex old new idx1) (replaceIndex old new idx2)
  IEq idx1 idx2 -> IEq (replaceIndex old new idx1) (replaceIndex old new idx2)
  BNeg bidx -> BNeg (replaceBoolIndex old new bidx)
  ITrue -> ITrue
  IFalse -> IFalse

replaceSort :: Ident -> Ident -> Sort -> Sort
replaceSort old new sort = case sort of
  Subsort idx s bidx -> Subsort idx (replaceSort old new s) (replaceBoolIndex old new bidx)
  IntSort -> IntSort
  Pair s1 s2 -> Pair (replaceSort old new s1) (replaceSort old new s2)

replaceIVarInt :: Ident -> IntIndex -> TypeExp -> TypeExp
replaceIVarInt old new t = case t of
  PlainInt -> PlainInt
  ArrayType Nothing tp -> ArrayType Nothing (replaceIVarInt old new tp)
  ArrayType (Just idx) tp -> ArrayType (Just (replaceIndexInt old new idx)) (replaceIVarInt old new tp)
  TupleType tps -> TupleType $ map (replaceIVarInt old new) tps
  TypeName n -> TypeName n
  IntPredType _i _b -> undefined
  BoolType b -> BoolType (replaceBoolIndexInt old new b)
  IntType idx -> IntType (replaceIndexInt old new idx)
  FunType t1 t2 -> FunType (replaceIVarInt old new t1) (replaceIVarInt old new t2)
  PiType ident s tp -> if ident == old then t else PiType ident (replaceSortInt old new s) (replaceIVarInt old new tp)
  SigType ident s tp -> if ident == old then t else SigType ident (replaceSortInt old new s) (replaceIVarInt old new tp)
  GuardedType b tp -> GuardedType (replaceBoolIndexInt old new b) (replaceIVarInt old new tp)
  AssertingType tp b ->  AssertingType (replaceIVarInt old new tp) (replaceBoolIndexInt old new b)
  ETVar v -> ETVar v
  PolyType ident tp -> PolyType ident (replaceIVarInt old new tp)
  UTVar v -> UTVar v

replaceIndexInt :: Ident -> IntIndex -> IntIndex -> IntIndex
replaceIndexInt old new idx1 = case idx1 of
  IndexConst c -> IndexConst c
  IndexVar ident -> if ident == old then new else IndexVar ident
  ExIVar ident -> if ident == old then new else ExIVar ident

replaceBoolIndexInt :: Ident -> IntIndex -> BoolIndex -> BoolIndex
replaceBoolIndexInt old new bi = case bi of
  ILess idx1 idx2 -> ILess (replaceIndexInt old new idx1) (replaceIndexInt old new idx2)
  ISLess idx1 idx2 -> ISLess (replaceIndexInt old new idx1) (replaceIndexInt old new idx2)
  IEq idx1 idx2 -> IEq (replaceIndexInt old new idx1) (replaceIndexInt old new idx2)
  BNeg bidx -> BNeg (replaceBoolIndexInt old new bidx)
  ITrue -> ITrue
  IFalse -> IFalse
  IAnd i1 i2 -> IAnd (replaceBoolIndexInt old new i1) (replaceBoolIndexInt old new i2)

replaceSortInt :: Ident -> IntIndex -> Sort -> Sort
replaceSortInt old new sort = case sort of
  Subsort idx s bidx -> Subsort idx (replaceSortInt old new s) (replaceBoolIndexInt old new bidx)
  IntSort -> IntSort
  Pair s1 s2 -> Pair (replaceSortInt old new s1) (replaceSortInt old new s2)

replaceTVar :: HasCallStack => Ident -> TypeExp -> TypeExp -> TypeExp
replaceTVar old new t = case t of
  PlainInt -> PlainInt
  ArrayType i tp -> ArrayType i (replaceTVar old new tp)
  TupleType tps -> TupleType $ map (replaceTVar old new) tps
  TypeName n -> TypeName n
  IntPredType _i _b -> undefined
  BoolType b -> BoolType b
  IntType idx -> IntType idx
  FunType t1 t2 -> FunType (replaceTVar old new t1) (replaceTVar old new t2)
  PiType ident s tp -> PiType ident s (replaceTVar old new tp)
  GuardedType b tp -> GuardedType b (replaceTVar old new tp)
  UTVar ident -> if ident == old then new else UTVar ident
  ETVar ident -> if ident == old then new else ETVar ident
  SigType ident s tp -> SigType ident s (replaceTVar old new tp)
  AssertingType tp b -> AssertingType (replaceTVar old new tp) b
  PolyType ident tp -> if ident == old then t else PolyType ident (replaceTVar old new tp)
