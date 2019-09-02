{-# LANGUAGE FlexibleContexts #-}

module RefinedFuthark.Constraints (typeCheck, Constraint(..), Prop(..)) where

import RefinedFuthark.Syntax
import RefinedFuthark.Transform
import Data.Foldable (foldrM)
import Data.Set (union,delete,Set,empty,singleton)
import qualified Data.Map as M

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

--import Prelude (undefined,return)
--import Data.Maybe (Maybe(..))

type TypeM = ReaderT Ctx (StateT Env (Except Error))
type Error = String
data Ctx = Ctx TypeContext ValContext
data Env = Env (Integer, M.Map Ident Sort)

data Constraint
  = Top -- Always true
  | Conj Constraint Constraint
  | Impl Prop Constraint
  | Prop Prop -- A Proposition is also a constraint
  | Forall Ident Sort Constraint
  | Exists Ident Sort Constraint
  deriving (Show,Eq)

data Prop
  = TT
  | FF
  | And Prop
  | Or Prop
  | BoolPred BoolIndex
  deriving (Show,Eq)


--data Context = Context TypeContext ValContext

data TypeContext = TypeContext (M.Map Ident Sort)
data ValContext = ValContext (M.Map Ident TypeExp)

checkProgram :: Program -> TypeM Constraint
checkProgram [dec] = checkDec dec
checkProgram _ = throwError "Cannot typecheck this kind of program yet"

checkDec :: Dec -> TypeM Constraint
checkDec (ValDec _ident tps (p:ps) rt e) = fst <$> case (curryfy (lparam p) (map lparam ps) (Just rt) e) of
  Lambda p' rt' e' -> makeLambda tps p' rt' e'
  _ -> error "should not happen"
checkDec (ValDec _ident _tps [] rt e) = checkExp e rt
checkDec (ImportDec _) = return Top

typeCheck :: Program -> Either Error Constraint
typeCheck p = runExcept (evalStateT (runReaderT (checkProgram p) ctx) env)
  where ctx = prelude
        env = initialEnv

initialEnv :: Env
initialEnv = Env (0,M.empty)

prelude :: Ctx
prelude = Ctx (TypeContext M.empty) (ValContext (M.fromList [indexType,mapType]))
  where indexType = ("_index", PiType "n" IntSort (PiType "i" (Subsort "i" IntSort (ILess (IndexVar "i") (IndexVar "n")))
          (FunType (ArrayType (Just (IndexVar "n")) PlainInt)
            (FunType (IntType (IndexVar "i")) PlainInt))))
        mapType = ("map",PlainInt)

checkExp :: Exp -> TypeExp -> TypeM Constraint
checkExp e t = case e of
  IfThenElse e1 e2 e3 -> checkIf e1 e2 e3 t
  Let binds e' -> checkLet binds e' t
  Lambda p ta e1 -> checkLambda p ta e1 t --(makePiType tps t)
  Var name -> checkVar name t
  UnOp op e1 -> checkExp (Apply (Var (unOpName op)) [e1]) t
  Apply e1 e2 -> checkApply e1 e2 t
  OpSection op -> checkExp (Var (opName op)) t
  Index arr e2 -> checkExp (Apply (Var "_index") [Var arr, e2]) t
  IntLit i -> checkLit i t
  FloatLit _f -> undefined
  BinOp op e1 e2 -> checkExp (Apply (Var (opName op)) [e1,e2]) t

makeType :: Exp -> TypeM (Constraint, TypeExp)
makeType e = case e of
  Apply e1 [e2] -> makeApply e1 e2
  Var qualName -> do
    t <- lookupVar qualName
    return (Top,t)
  Index arr e2 -> makeType (Apply (Var "_index") [Var arr, e2])
  Lambda p rt e1 -> makeLambda [] p rt e1
  IntLit n -> return (Top,IntType (IndexConst n))
  _ -> throwError ("Cannot synthesize type for " ++ prettyExp e)

unOpName :: UnOp -> QualName
unOpName = undefined

opName :: Operator -> QualName
opName = undefined

lookupVar :: QualName -> TypeM TypeExp
lookupVar qualName = do
  Ctx _ (ValContext binds) <- ask
  case M.lookup qualName binds of
    Just t -> return t
    Nothing -> throwError $ "unbound variable " ++ qualName

makeLambda :: [TypeParam] -> LParam -> Maybe TypeExp -> Exp -> TypeM (Constraint, TypeExp)
makeLambda tps (ident, Just pt) (Just rt) e = do
  c1 <- checkLambda (ident, Just pt) (Just rt) e t
  return (c1, t)
  where t = makePiType tps (FunType pt rt)
makeLambda _ _ Nothing _ = throwError "Cannot infer type for lambda with no return type annotation"
makeLambda _ _ _ _ = throwError "Cannot infer type for lambda with no parameter annotation"

makeApply :: Exp -> Exp -> TypeM (Constraint, TypeExp)
makeApply e1 e2 = do
  (c1,t) <- makeType e1
  (at,rt) <- f t
  c2 <- checkExp e2 at
  return (Conj c1 c2, rt)
  where f t = case t of
          FunType at rt -> do
            return (at,rt)
          PiType ident sort t' -> do
            v <- newIVar sort
            f (replaceIVar ident v t')
          _ -> unexpectedType "function type" t

newIVar :: Sort -> TypeM Ident
newIVar s = do
  (Env (n,env)) <- get
  let ident = show n
  put (Env (n+1,M.insert ident s env))
  return ident

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

getVarsInType :: TypeExp -> Set Ident
getVarsInType tp = case tp of
  PlainInt -> empty
  ArrayType Nothing t -> getVarsInType t
  ArrayType (Just idx) t -> (getVarsInIndex idx) `union` (getVarsInType t)
  TupleType tps -> foldMap getVarsInType tps
  TypeName _n -> empty
  IntPredType _i _b -> undefined
  BoolType b -> getVarsInBoolIndex b
  IntType idx -> getVarsInIndex idx
  FunType t1 t2 -> getVarsInType t1 `union` getVarsInType t2
  PiType ident s t -> getVarsInSort s `union` delete ident (getVarsInType t)

getVarsInSort :: Sort -> Set Ident
getVarsInSort sort = case sort of
  Subsort idx s bidx -> (getVarsInSort s) `union` delete idx (getVarsInBoolIndex bidx) --TODO the same var multiple times
  IntSort -> empty
  Pair s1 s2 -> (getVarsInSort s1) `union` (getVarsInSort s2)

getVarsInIndex :: IntIndex -> Set Ident
getVarsInIndex idx = case idx of
  IndexConst _ -> empty
  IndexVar ident -> singleton ident

getVarsInBoolIndex :: BoolIndex -> Set Ident
getVarsInBoolIndex bidx = case bidx of
  ILess idx1 idx2 ->  getVarsInIndex idx1 `union` getVarsInIndex idx2
  IEq idx1 idx2 -> getVarsInIndex idx1 `union` getVarsInIndex idx2
  BNeg bidx' -> getVarsInBoolIndex bidx'
  ITrue -> empty
  IFalse -> empty

checkIf :: Exp -> Exp -> Exp -> TypeExp -> TypeM Constraint
checkIf e1 e2 e3 t = do
  (c1, bt) <- makeType e1
  case bt of
    BoolType i -> do
      c2 <- checkExp e2 t
      c3 <- checkExp e3 t
      return (c1 `Conj` Impl (BoolPred i) c2 `Conj` Impl (BoolPred (BNeg i)) c3)
    t2 -> unexpectedType "bool type" t2

checkLambda :: LParam -> Maybe TypeExp -> Exp -> TypeExp -> TypeM Constraint
checkLambda (pident, _pt) _ta e t = case t of
  PiType ident sort t' -> do
    c <- local (bindSort ident sort) (checkLambda (pident, _pt) _ta e t')
    return (Forall ident sort c)
  FunType at rt -> local (expandContext pident at) (checkExp e rt)
  _ -> unexpectedType "function type" t

unexpectedType :: String -> TypeExp -> TypeM a
unexpectedType s t = throwError $ "Expected " ++ s ++ " but got " ++ prettyType t

prettyType :: TypeExp -> String
prettyType t = show t

prettyExp :: Exp -> String
prettyExp e = show e

checkApply :: Exp -> [Exp] -> TypeExp -> TypeM Constraint
checkApply e1 e2 t1 = do
  (c1,t2) <- makeType (Apply e1 e2)
  closeExists t1 t2 (Prop (BoolPred (typeEq t1 t2)) `Conj` c1)

checkLit :: Integer -> TypeExp -> TypeM Constraint
checkLit n t1 = do
  (Top, t2) <- makeType (IntLit n)
  closeExists t1 t2 (Prop (BoolPred (typeEq t1 t2)))

checkVar :: QualName -> TypeExp -> TypeM Constraint
checkVar name t1 = do
  (Top,t2) <- makeType (Var name)
  closeExists t1 t2 (Prop (BoolPred (typeEq t1 t2)))

closeExists :: TypeExp -> TypeExp -> Constraint -> TypeM Constraint
closeExists t1 t2 c = do
  env <- get
  ctx <- ask
  let psi = localPsi t2 t1 env ctx
  deleteIVars psi
  -- check if t1 == t2
  -- existential quantify over all variables only in t2
  return (M.foldrWithKey f c psi)
  where f ident sort c' = Exists ident sort c'

checkLet :: [(Ident, Maybe TypeExp, Exp)] -> Exp -> TypeExp -> TypeM Constraint
checkLet binds e t = do
  (g',c1) <- foldrM g (id, Top) binds
  c2 <- g' (checkExp e t)
  return (Conj c1 c2)
  where g (i, t1, e1) (f, c) = do
          (c',t2) <- case t1 of
            Just t' -> do
              c' <- f (checkExp e1 t')
              return (c',t')
            Nothing -> makeType e1
          return (local (expandContext i t2) . f, Conj c c')

deleteIVars :: M.Map Ident Sort -> TypeM ()
deleteIVars vars = do
  Env (n,env) <- get
  let env' = env `M.withoutKeys` M.keysSet vars
  put (Env (n,env'))

expandContext :: Ident -> TypeExp -> Ctx -> Ctx
expandContext i tp (Ctx tc (ValContext vc)) = Ctx tc (ValContext (M.insert i tp vc)) 

bindSort :: Ident -> Sort -> Ctx -> Ctx
bindSort ident sort (Ctx (TypeContext tc) vc) = Ctx (TypeContext (M.insert ident sort tc)) vc

localPsi :: TypeExp -> TypeExp -> Env -> Ctx -> M.Map Ident Sort
localPsi t1 t2 (Env (_,sorts)) (Ctx _ (ValContext vars)) = psi1
  where psi1 = sorts `M.restrictKeys` getVarsInType t1 `M.withoutKeys` psi2
        psi2 = getVarsInType t2 `union` foldMap getVarsInType (M.elems vars)

typeEq :: TypeExp -> TypeExp -> BoolIndex
typeEq (IntType i1) (IntType i2) = IEq i1 i2
typeEq (TypeName n1) (TypeName n2) = if n1 == n2 then ITrue else IFalse
typeEq _ _ = undefined
  --throwError ("Cannot compare types " ++ prettyType t1 " and " ++ prettyType t2)
