
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module RefinedFuthark.TypeCheck (typeCheck, ContextItem(..)) where

import GHC.Stack

import RefinedFuthark.Syntax
import RefinedFuthark.Util
import RefinedFuthark.Transform

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as M
import Data.Maybe (mapMaybe)

type TypeM = ReaderT Ctx (StateT Env (Except Error))
type Error = String
data Ctx = Ctx
type ExVarMap = M.Map Var MonoType
data Env = Env { freshNameCount :: Integer
               , context :: Context
               , exVarMap :: ExVarMap
               , constraints :: [Constraint]
               } -- todo: should be monotype or index object

type Context = [ContextItem]

data Constraint
  = Prop BoolIndex
  | Forall Ident Constraint
  | Impl BoolIndex Constraint
  deriving Show

type Var = String

data MonoType =
    ExIndex IntIndex
  | ExType TypeExp
  deriving Show

data ContextItem
  = UVar Var
  | ExVar Var -- todo: should only be able to be monotype or index object
  | ExpVar Var TypeExp
  | Marker Var
  | Cond BoolIndex
  | Sub TypeExp TypeExp
  deriving Show

checkProgram :: Program -> TypeM [Constraint]
checkProgram decs = do
  mapM_ checkDec decs
  cs <- gets constraints
  mapM_ solveConstraint cs
  return cs
-- checkProgram _ = throwError "Cannot typecheck this kind of program yet"

checkDec :: Dec -> TypeM ()
checkDec (ValDec ident tps (p:ps) rt e) = checkType e' t >> addVar ident t
  where e' = transformExp p ps rt e --(curryfy (lparam p) (map lparam ps) (Just rt) e)
        t = transformParams tps p ps rt
checkDec (ValDec ident _tps [] t e) = checkType e t' >> addVar ident t'
  where t' = transformType t
checkDec (ImportDec _) = return () -- throwError "Cannot typecheck imports yet"

typeCheck :: Program -> Either Error [Constraint]
typeCheck p = runExcept (evalStateT (runReaderT (checkProgram p) ctx) env)
  where ctx = Ctx
        env = initialEnv

initialEnv :: Env
initialEnv = Env { freshNameCount = 0, context = prelude, exVarMap = M.empty, constraints = [] }

prelude :: Context
prelude =
  [
   ExpVar "undefined" (PolyType "_" $ UTVar "_")
  ,ExpVar "iota_test" (PiType "a" IntSort (FunType (IntType (IndexVar "a")) (ArrayType (Just (IndexVar "a")) (SigType "n2" IntSort (AssertingType (IntType (IndexVar "n2")) (ILess (IndexConst 0) (IndexVar "n2") `IAnd` ISLess (IndexVar "n2") (IndexVar "a")))))))
  ,ExpVar "rep_iota" (PiType "a" IntSort (ArrayType (Just (IndexVar "a")) intType `FunType` (SigType "l" IntSort (ArrayType (Just (IndexVar "l")) (SigType "m" IntSort (AssertingType (IntType (IndexVar "m")) (ILess (IndexConst 0) (IndexVar "m") `IAnd` ISLess (IndexVar "m") (IndexVar "a"))))))))
  ,ExpVar "map" $ PolyType "a" $ PolyType "b" $ PiType "n" IntSort $ (UTVar "a" `FunType` UTVar "b") `FunType` (ArrayType (Just (IndexVar "n")) (UTVar "a") `FunType` ArrayType (Just (IndexVar "n")) (UTVar "b"))
  ,ExpVar "map2" $ PolyType "a" $ PolyType "b" $ PiType "n" IntSort $ (ArrayType (Just (IndexVar "n")) (UTVar "a") `FunType` ((UTVar "a" `FunType` UTVar "b") `FunType` ArrayType (Just (IndexVar "n")) (UTVar "b")))
  ,ExpVar "id" $ PolyType "a" $ UTVar "a" `FunType` UTVar "a"
  ,ExpVar "const" $ PolyType "a" $ UTVar "a" `FunType` (UTVar "a" `FunType` UTVar "a")
  ,ExpVar "idInt" (FunType intType intType)
  ,ExpVar "ints" (PiType "l" IntSort (FunType (IntType (IndexVar "l")) (ArrayType (Just (IndexVar "l")) intType)))
  ,ExpVar "get2" (PiType "n" IntSort (GuardedType (ILess (IndexConst 0) (IndexVar "n")) (FunType (IntType (IndexVar "n")) intType)))
  ,ExpVar "get" (PolyType "a" (PiType "n" IntSort (PiType "m" IntSort (FunType (ArrayType (Just (IndexVar "n")) (UTVar "a")) (FunType (IntType (IndexVar "m")) (UTVar "a"))))))
  ,ExpVar "get3" (PolyType "a" (PiType "n" IntSort (PiType "m" IntSort ((IntType (IndexVar "m")) `FunType` (ArrayType (Just (IndexVar "n")) (UTVar "a") `FunType` (UTVar "a"))))))
  -- ,ExpVar "x" (SigType "a" IntSort (AssertingType (IntType (IndexVar "a")) (ILess (IndexConst 0) (IndexVar "a"))))
  -- ,ExpVar ".index" (PolyType "a" (PiType "n" IntSort (PiType "m" IntSort (GuardedType (IAnd (ILess (IndexConst 0) (IndexVar "m")) (ISLess (IndexVar "m") (IndexVar "n"))) (FunType (ArrayType (Just (IndexVar "n")) (UTVar "a")) (FunType (IntType (IndexVar "m")) (UTVar "a")))))))
  ,ExpVar ".index" (PolyType "a" (PiType "n" IntSort (FunType (ArrayType (Just (IndexVar "n")) (UTVar "a")) (FunType (SigType "m" IntSort (AssertingType (IntType (IndexVar "m")) (IAnd (ILess (IndexConst 0) (IndexVar "m")) (ISLess (IndexVar "m") (IndexVar "n"))))) (UTVar "a")))))
  ,ExpVar "length" $ PolyType "e" $ PiType "l" IntSort $ ArrayType (Just (IndexVar "l")) (UTVar "e") `FunType` IntType (IndexVar "l")
  -- ,UVar "k"
  -- ,Cond (ILess (IndexConst 0) (IndexVar "k"))
  -- ,Cond (ISLess (IndexVar "k") (IndexVar "a"))
  -- ,ExpVar "i" (IntType (IndexVar "k"))
  ]

intType :: TypeExp
intType = SigType "n" IntSort (IntType (IndexVar "n"))
-- intType = TypeName "i32"

natType :: TypeExp
natType = SigType "n" IntSort (AssertingType (IntType (IndexVar "n")) (ILess (IndexConst 0) (IndexVar "n")))

checkType :: Exp -> TypeExp -> TypeM ()
checkType e t = case e of
  Lambda p ta e1 -> checkLambda p ta e1 t
  Let binds e'-> checkLet binds e' t
  Var _ -> checkSub e t
  Apply _ _ -> checkSub e t
  IntLit _ -> checkSub e t
  Index _ _ -> checkSub e t
  _ -> throwError $ "Cannot yet check syntactic form "
                    ++ prettyExp e

checkSub :: Exp -> TypeExp -> TypeM ()
checkSub e t = do
  t' <- synthType e
  t' `isSubtypeOf` t

checkLet :: [(Ident, Maybe TypeExp, Exp)] ->
            Exp -> TypeExp -> TypeM ()
checkLet [] e2 t2 = checkType e2 t2
checkLet ((ident,ta,e1):binds) e2 t2 = do
  t' <- case ta of
    Nothing -> synthType e1
    Just t'' -> checkType e1 t'' >> return t''
  c <- getContext
  m <- getExVarMap
  checkLet1 (replaceContext c m t')
  where
    checkLet1 t = case t of
      AssertingType t' p -> do
        v <- newMarker
        consCond p
        checkLet1 t'
        removeAfter v
      SigType ident' _sort t' -> do
        consContext (UVar ident')
        checkLet1 t'
        removeAfter ident'
      _ -> do
        addVar ident t
        c <- getContext
        m <- getExVarMap
        checkLet binds e2 (replaceContext c m t2)
        removeAfter ident

consCond :: BoolIndex -> TypeM ()
consCond (IAnd p1 p2) = consCond p1 >> consCond p2
consCond p = consContext (Cond p)

checkLambda :: HasCallStack => LParam -> Maybe TypeExp -> Exp -> TypeExp -> TypeM ()
checkLambda (ident, _) _rt e (FunType t1 t2) = do
  addVar ident t1
  checkType e t2
  removeAfter ident
-- checkLambda (ident, _) _rt e (ETVar v) = do
--   v2 <- newEVarBefore v
--   v1 <- newEVarBefore v2
--   solveEVar v (ExType (FunType (ETVar v1) (ETVar v2)))
--   addVar ident (ETVar v1)
--   checkType e (ETVar v2)
--   removeAfter v1
checkLambda p rt e (PiType ident1 _sort t) = do
  consContext (UVar ident1)
  checkLambda p rt e t
  removeAfter ident1
checkLambda p rt e (PolyType ident1 t) = do
  consContext (UVar ident1)
  checkLambda p rt e t
  removeAfter ident1
checkLambda _ _ _ t = unexpectedType "function type" t

isSubtypeOf :: HasCallStack => TypeExp -> TypeExp -> TypeM ()
isSubtypeOf (ETVar v1) (ETVar v2) = do
  c <- getContext
  v <- go c
  insertAfter v (Sub (ETVar v1) (ETVar v2))
  where go [] = throwError "Tried to determine subtype of variable not in scope"
        go (ExVar v : _)
          | v == v1 = return v1
          | v == v2 = return v2
        go (_ : c) = go c
isSubtypeOf (ETVar v) t2 = insertAfter v (Sub (ETVar v) t2)
isSubtypeOf t1 (ETVar v) = insertAfter v (Sub t1 (ETVar v))
isSubtypeOf t1 t2 = case t2 of
  PolyType _ _ -> negSubtype t1 t2
  PiType _ _ _-> negSubtype t1 t2
  SigType _ _ _ -> posSubtype t1 t2
  _ -> case t1 of
    PolyType _ _ -> negSubtype t1 t2
    PiType _ _ _ -> negSubtype t1 t2
    SigType _ _ _ -> posSubtype t1 t2
    _ -> nonpolSubtype t1 t2

negSubtype :: TypeExp -> TypeExp -> TypeM ()
negSubtype t1 (PiType _ident _sort _t) = undefined -- R
negSubtype t1 (PolyType _ _) = undefined -- R
negSubtype (PiType _ident _sort _t) t2 = undefined -- L
negSubtype (PolyType ident1 t1') t2 = do -- L
  m <- newMarker
  v <- newEVar TypeSort
  negSubtype (replaceTVar ident1 (ETVar v) t1') t2
  checkExVar v
  removeAfter m
negSubtype t1 t2 = case t1 of
  SigType _ _ _ -> posSubtype t1 t2
  _ -> case t2 of
    SigType _ _ _ -> posSubtype t1 t2
    _ -> nonpolSubtype t1 t2

posSubtype :: TypeExp -> TypeExp -> TypeM ()
posSubtype (SigType ident1 sort1 t1') t2 = do
  consContext (UVar ident1)
  posSubtype t1' t2
  removeAfter ident1
posSubtype t1 (SigType ident sort t2') = do
  m <- newMarker
  v <- newEVar sort
  posSubtype t1 (replaceIVarInt ident (ExIVar v) t2')
  checkExVar v
  removeAfter m
posSubtype t1 t2 = case t1 of
  PiType _ _ _ -> negSubtype t1 t2
  PolyType _ _ -> negSubtype t1 t2
  _ -> case t2 of
    PiType _ _ _ -> negSubtype t1 t2
    PolyType _ _ -> negSubtype t1 t2
    _ -> nonpolSubtype t1 t2

nonpolSubtype :: TypeExp -> TypeExp -> TypeM ()
nonpolSubtype (ETVar v) t2 = insertAfter v (Sub (ETVar v) t2)
nonpolSubtype t1 (ETVar v) = insertAfter v (Sub t1 (ETVar v))
nonpolSubtype (AssertingType t1' p) t2 = do
  v <- newMarker
  consCond p
  nonpolSubtype t1' t2
  removeAfter v
nonpolSubtype t1 (AssertingType t2' p) = do
  nonpolSubtype t1 t2'
  c <- getContext
  m <- getExVarMap
  checkProp (replaceProp c m p)
nonpolSubtype t1 t2 = typeEquiv t1 t2

typeEquiv :: HasCallStack => TypeExp -> TypeExp -> TypeM ()
typeEquiv (IntType i1) (IntType i2) = indexEq i1 i2
typeEquiv (ArrayType (Just i1) t1) (ArrayType (Just i2) t2) = do
  indexEq i1 i2
  m <- getExVarMap
  c <- getContext
  typeEquiv (replaceContext c m t1) (replaceContext c m t2)
typeEquiv (FunType t1 t2) (FunType t1' t2') = do
  typeEquiv t1 t1'
  m <- getExVarMap
  c <- getContext
  typeEquiv (replaceContext c m t2) (replaceContext c m t2')
typeEquiv (TypeName n1) (TypeName n2)
  | n1 == n2 = return ()
typeEquiv (UTVar v1) (UTVar v2)
  | v1 == v2 = return ()
typeEquiv (ETVar v1) (ETVar v2)
  | v1 == v2 = return ()
typeEquiv (ETVar v) t = instType v t
typeEquiv t (ETVar v) = instType v t
typeEquiv (SigType _ _ t1') (SigType _ _ t2') = typeEquiv t1' t2'
typeEquiv t1 t2 = throwError $ "Expected type " ++ prettyType t2 ++ " but got type " ++ prettyType t1

indexEq :: IntIndex -> IntIndex -> TypeM ()
indexEq (IndexConst n) (IndexConst m)
  | n == m = return ()
indexEq (IndexVar v1) (IndexVar v2)
  | v1 == v2 = return ()
indexEq (ExIVar v1) (ExIVar v2)
  | v1 == v2 = return ()
indexEq (ExIVar v) t = instantiateIVar v t
indexEq t (ExIVar v) = instantiateIVar v t
indexEq i1 i2 = throwError $ "index eq: Expected type " ++ prettyType (IntType i2) ++ " but got type " ++ prettyType (IntType i1)

instantiateIVar :: Var -> IntIndex -> TypeM ()
instantiateIVar v i = case i of
  ExIVar v2 -> do
    c <- getContext
    (v1',v2') <- go [ v' | ExVar v' <- c ]
    solveEVar v1' (ExIndex (ExIVar v2'))
    where go [] = throwError "Tried to instantiate variable not in context"
          go (v':_)
            | v' == v = return (v,v2)
            | v' == v2 = return (v2,v)
          go (_:vs) = go vs
  IndexVar iv -> do
    c <- getContext
    if iv `elem` [ v' | UVar v' <- dropWhile f c] then solveEVar v (ExIndex i) else throwError $ "Index variable " ++ iv ++ " not in scope"
    where f (ExVar v') = v' /= v
          f _ = True
  IndexConst _ -> solveEVar v (ExIndex i)

solveEVar :: Var -> MonoType -> TypeM ()
solveEVar v i = do
  m <- getExVarMap
  let (r,m') = M.insertLookupWithKey (\_ x _ -> x) v i m
  case r of
    Just _ -> throwError ("Tried to instantiate existential variable twice, " ++ v ++ ", map: " ++ show m)
    Nothing -> putExVarMap m'

instType :: HasCallStack => Var -> TypeExp -> TypeM ()
instType v t = case t of
  TypeName n -> solveEVar v (ExType t)
  UTVar _ -> solveEVar v (ExType t)
  ArrayType (Just i) t -> do
    v1 <- newEVarBefore v
    v2 <- newEVarBefore v1
    solveEVar v  (ExType $ ArrayType (Just (ExIVar v1)) (ETVar v2))
    instantiateIVar v1 i
    c <- getContext
    m <- getExVarMap
    instType v2 (replaceContext c m t)
  SigType _ _ _ -> solveEVar v (ExType t) -- TODO free variables
  -- SigType ident sort t' -> do
  --   v' <- newEVarBefore v
  --   solveEVar v (ExType (SigType ident sort (ETVar v')))
  --   instType v' t'
  -- AssertingType t' p -> do
  --   v' <- newEVarBefore v
  --   solveEVar v (ExType (AssertingType (ETVar v') p))
  --   instType v' t'
  ETVar v2 -> do
    c <- getContext
    (v1',v2') <- go [ v' | ExVar v' <- c ]
    solveEVar v1' (ExType (ETVar v2'))
    where go [] = throwError "Tried to instantiate variable not in context"
          go (v':_)
            | v' == v = return (v,v2)
            | v' == v2 = return (v2,v)
          go (_:vs) = go vs
  IntType i -> do
    v' <- newEVarBefore v
    solveEVar v (ExType (IntType (ExIVar v')))
    instantiateIVar v' i
  FunType t1 t2 -> do
    v1 <- newEVarBefore v
    v2 <- newEVarBefore v1
    solveEVar v (ExType (FunType (ETVar v1) (ETVar v2)))
    instType v1 t1
    c <- getContext
    m <- getExVarMap
    instType v2 (replaceContext c m t2)
  AssertingType _ _ -> solveEVar v (ExType t)
  _ -> throwError (show t)

synthType :: HasCallStack => Exp -> TypeM TypeExp
synthType e = case e of
  IntLit i -> return (IntType (IndexConst i))
  Apply f s -> synthType f >>= checkSpine s
  Var qualName -> lookupVar qualName
  UnOp op e1 -> synthType (Apply (Var (unOpName op)) [e1])
  OpSection op -> synthType (Var (opName op))
  Index arr e2 -> synthType (Apply (Var ".index") [Var arr, e2])
  FloatLit _f -> undefined
  BinOp op e1 e2 -> synthType (Apply (Var (opName op)) [e1,e2])
  Lambda p ta e' -> synthLambda p ta e'
  _ -> throwError ("Cannot synthesize type for " ++ prettyExp e)


checkSpine :: HasCallStack => [Exp] -> TypeExp -> TypeM TypeExp
checkSpine [] t = return t
checkSpine s (PiType ident sort t) = do
  v <- newEVar sort
  t' <- checkSpine s (replaceIVarInt ident (ExIVar v) t)
  checkExVar v
  c <- getContext
  m <- getExVarMap
  return (replaceContext c m t')
checkSpine s (PolyType ident t) = do
  v <- newEVar TypeSort
  t' <- checkSpine s (replaceTVar ident (ETVar v) t)
  checkExVar v
  c <- getContext
  m <- getExVarMap
  return (replaceContext c m t')
checkSpine (e:s) (FunType t1 t2) = do
  checkType e t1
  c <- getContext
  m <- getExVarMap
  checkSpine s (replaceContext c m t2)
checkSpine s (GuardedType p t) = do
  t' <- checkSpine s t
  c <- getContext
  m <- getExVarMap
  checkProp (replaceProp c m p)
  return t'
-- checkSpine s (ETVar v) = do
  -- v1 <- newEVarBefore v
  -- v2 <- newEVarBefore v1
  -- let ft = FunType (ETVar v1) (ETVar v2)
  -- solveEVar v (ExType ft)
  -- t' <- checkSpine s ft
  -- checkExVar v1
  -- checkExVar v2
  -- return t'
checkSpine _ t = unexpectedType "function type" t

checkExVar :: Var -> TypeM ()
checkExVar v = do
  c <- getContext
  m <- getExVarMap
  let (c1,c2) = go c
  case c2 of
    (Sub t1 t2) : c3
      | unsolved v m -> do
        typeEquiv t1 t2
        checkExVar v
      | otherwise -> do
        isSubtypeOf (replaceContext c m t1) (replaceContext c m t2)
        putContext (c1 ++ c3)
        checkExVar v
    _ -> return ()
  where go (ExVar v' : c)
          | v' == v = ([ExVar v'],c)
        go (item:c) = (item:c1,c2)
          where (c1,c2) = go c

unsolved :: Var -> ExVarMap -> Bool
unsolved v m = M.notMember v m

synthLambda :: LParam -> Maybe TypeExp -> Exp -> TypeM TypeExp
synthLambda (ident, Just pt) (Just rt) e = do
  checkLambda (ident, Just pt) (Just rt) e t
  return t
  where t = FunType pt rt-- makePiType tps (FunType pt rt)
synthLambda _ Nothing _ = throwError "Cannot infer type for lambda with no return type annotation"
synthLambda _ _ _ = throwError "Cannot infer type for lambda with no parameter type annotation"


checkProp :: BoolIndex -> TypeM ()
-- checkProp ITrue = return ()
-- checkProp (IAnd i1 i2) = checkProp i1 >> checkProp i2
checkProp i = do
  -- c <- getContext
  -- m <- getExVarMap
  ctx <- getContext
  env @ Env { constraints = c } <- get
  let p = foldl f (Prop i) ctx
  put env { constraints = p : c}
  -- if i `elem` [p | Cond p <- c] then return () else throwError $
  --   "Cannot prove proposition " ++ prettyProp i ++ ",context: " ++ show [p | Cond p <- c] ++ " " ++ show m

-- checkProp i = throwError $ "Cannot prove proposition " ++ prettyProp i
  where f c (Cond p) = Impl p c
        f c (UVar v) = Forall v c
        f c  _ = c
---------------------
-- Utility functions
---------------------

lookupVar :: QualName -> TypeM TypeExp
lookupVar qualName = do
  c <- getContext
  m <- getExVarMap
  case lookup qualName [(v,t) | ExpVar v t <- c] of
    Just t -> return (replaceContext c m t)
    Nothing -> throwError $ "Unbound variable " ++ qualName ++ ", " ++ show c

replaceContext :: Context -> ExVarMap -> TypeExp -> TypeExp
replaceContext c m t = foldr f t exvars
  where exvars = mapMaybe (\v -> (v,) <$> M.lookup v m) [ v | ExVar v <- c]
        f (v,i) t' = replaceMTVar v (replace i) t'
        replace (ExType t') = ExType (replaceContext c m t')
        replace mt = mt

replaceProp :: Context -> ExVarMap -> BoolIndex -> BoolIndex
replaceProp c m p = foldr f p exvars
  where exvars = [ (v,i) | (v,Just (ExIndex i)) <- [ (v,M.lookup v m) | ExVar v <- c]]
        f (v,i) p' = replaceBoolIndexInt v i p'


replaceMTVar :: Var -> MonoType -> TypeExp -> TypeExp
replaceMTVar v (ExType t1) t2 = replaceTVar v t1 t2
replaceMTVar v (ExIndex i) t = replaceIVarInt v i t

newEVar :: Sort -> TypeM Var
newEVar _s = do
  env @ Env { freshNameCount = n, context = c } <- get
  let ident = show n
  put env { freshNameCount = n+1 , context = ExVar ident : c }
  return ident

newEVarBefore :: Var -> TypeM Var
newEVarBefore v = do
  env @ Env { freshNameCount = n, context = c } <- get
  let v2 = show n
  put env { freshNameCount = n+1 , context = go v2 c }
  return v2
  where go v2 ((ExVar v'): c') | v' == v = ExVar v : ExVar v2 : c'
        go v2 (item:c') = item : go v2 c'
        go _ _ = []

insertAfter :: HasCallStack => Var -> ContextItem -> TypeM ()
insertAfter v item = do
  c <- getContext
  putContext (go c)
  where go [] = error $ "variable " ++ v ++ " not found in context"
        go (ExVar v' : c) | v' == v = (ExVar v : item : c)
        go (item' : c) = item' : go c

newMarker :: TypeM Var
newMarker = do
  env @ Env { freshNameCount = n, context = c } <- get
  let var = show n
  put env { freshNameCount = n+1 , context = Marker var : c }
  return var

getExVarMap :: TypeM ExVarMap
getExVarMap = do
  env <- get
  return (exVarMap env)

putExVarMap :: ExVarMap -> TypeM ()
putExVarMap m = do
  env <- get
  put env { exVarMap = m }

addVar :: Var -> TypeExp -> TypeM ()
addVar ident t = do
  c <- getContext
  putContext (ExpVar ident t : c)

removeAfter :: Var -> TypeM ()
removeAfter v = do
  c <- getContext
  putContext $ tail (dropWhile f c)
  where f v1 = case v1 of
          UVar v' -> v /= v'
          Marker v' -> v /= v'
          ExpVar v' _ -> v /= v'
          ExVar v' -> v /= v'
          _ -> True

getContext :: TypeM Context
getContext = do
  env <- get
  return (context env)

consContext :: ContextItem -> TypeM ()
consContext item = do
  c <- getContext
  putContext (item : c)

unOpName :: UnOp -> QualName
unOpName = undefined

opName :: Operator -> QualName
opName = undefined

unexpectedType :: String -> TypeExp -> TypeM a
unexpectedType s t = throwError $ "Expected " ++ s ++ " but got " ++ prettyType t

putContext :: Context -> TypeM ()
putContext c = do
  env <- get
  put env { context = c }

prettyExp :: Exp -> String
prettyExp e = show e

prettyType :: TypeExp -> String
prettyType t = show t

prettyProp :: BoolIndex -> String
prettyProp i = show i

solveConstraint :: Constraint -> TypeM ()
solveConstraint c = solveC [] [] c
  where  solveC :: [Ident] -> [BoolIndex] -> Constraint -> TypeM ()
         solveC ids props (Prop pr) = checkC props pr
         solveC ids props (Forall ident c) = solveC (ident:ids) props c
         solveC ids props (Impl pr c) = solveC ids (addProp pr props) c
         addProp (IAnd p1 p2) props = addProp p2 . addProp p1 $ props
         addProp p props = p:props
         checkC props (IAnd p1 p2) = checkC props p1 >> checkC props p2
         checkC props (ILess (IndexConst c1) (IndexConst c2))
           | c1 <= c2 = return ()
         checkC props (ISLess (IndexConst c1) (IndexConst c2))
           | c1 < c2 = return ()
         checkC props p = if elem p props then return () else throwError $ "Could not prove proposition: " ++ show p