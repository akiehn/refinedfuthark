
module RefinedFuthark.Transform where

import RefinedFuthark.Syntax

curryfy :: (Ident, Maybe TypeExp) -> [(Ident, Maybe TypeExp)] -> Maybe TypeExp -> Exp -> Exp
curryfy p ps t e = Lambda p t2 e2
  where f (ident, pt') (t', e') = (FunType <$> pt' <*> t', Lambda (ident, pt') t' e')
        (t2,e2) = foldr f (t,e) ps

makePiType :: [TypeParam] -> TypeExp -> TypeExp
makePiType tps t = foldr f t tps
  where f (SizeVar ident) tp = PiType ident IntSort tp
        f (TypeVar ident) tp = PolyType ident tp

makeFunType :: Param -> [Param] -> TypeExp  -> TypeExp
makeFunType (Param _ pt) ps rt = FunType (transformType pt) (foldr f (transformType rt) ps)
  where f (Param _ t') t = FunType (transformType t') t

transformParams :: [TypeParam] -> Param -> [Param] -> TypeExp -> TypeExp
transformParams tps p ps rt = makePiType tps (makeFunType p ps rt)

transformExp :: Param -> [Param] -> TypeExp -> Exp -> Exp
transformExp p ps rt e = (curryfy (lparam p) (map lparam ps) (Just rt) e)

lparam :: Param -> LParam
lparam (Param ident t) = (ident, Just t)

transformType :: TypeExp -> TypeExp
transformType t  = case t of
  ArrayType (Just i) t' -> ArrayType (Just i) (transformType t')
  ArrayType Nothing t' -> SigType "l" IntSort $ ArrayType (Just (IndexVar "l")) (transformType t')
  IntPredType ident pr -> SigType ident IntSort $ AssertingType (IntType (IndexVar ident)) pr
  ArrayPredType ident t' pr -> SigType ident IntSort $ AssertingType (ArrayType (Just (IndexVar ident)) t') pr
  IntType i -> IntType i
  TypeName "i32" -> SigType "n" IntSort (IntType (IndexVar "n"))
  TypeName "i32" -> TypeName "i32"
  TypeName v -> UTVar v
  FunType t1 t2 -> FunType (transformType t1) (transformType t2)
  _ -> error (show t)

erase :: [Dec] -> [Dec]
erase = map eraseDec

eraseDec :: Dec -> Dec
eraseDec (ValDec ident tps ps rt e) = ValDec ident tps (map eraseParam ps) (eraseType rt) (eraseExp e)
eraseDec dec = dec

eraseParam :: Param -> Param
eraseParam (Param name t) = (Param name (eraseType t))

eraseType :: TypeExp -> TypeExp
eraseType (IntPredType _ _) = TypeName "i32"
eraseType (ArrayPredType _ t _) = ArrayType Nothing (eraseType t)
eraseType (ArrayType i t) = ArrayType i (eraseType t)
eraseType (IntType _) = TypeName "i32"
eraseType t = t

eraseExp :: Exp -> Exp
eraseExp (Let binds e) = Let (map (\(ident,t,e) -> (ident,eraseType <$> t, eraseExp e)) binds) (eraseExp e)
eraseExp e = e