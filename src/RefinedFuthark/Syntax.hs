module RefinedFuthark.Syntax where

data Dec
  = ImportDec String
  | ValDec Ident [TypeParam] [Param] TypeExp Exp
  deriving Show

data TypeParam
  = TypeVar Ident
  | SizeVar Ident
  deriving Show

data Param = Param Ident TypeExp -- Right now parameters always have type annotations
  deriving Show

type LParam = (Ident, Maybe TypeExp)

data TypeExp
  = ArrayType (Maybe IntIndex) TypeExp -- always int index internal
  | TupleType [TypeExp]
  | TypeName QualName
  | IntPredType Ident BoolIndex
  | ArrayPredType Ident TypeExp BoolIndex
  | BoolType BoolIndex
  | PlainInt
  | IntType IntIndex -- extern extended futhark
  | FunType TypeExp TypeExp
  | PiType Ident Sort TypeExp -- internal only
  | SigType Ident Sort TypeExp -- internal only
  | UTVar Ident
  | ETVar Ident
  | GuardedType BoolIndex TypeExp -- internal only
  | AssertingType TypeExp BoolIndex -- internal only
  | PolyType Ident TypeExp
  deriving Show

data IntIndex
  = IndexConst Integer
  | IndexVar Ident
  | ExIVar Ident
  deriving (Show,Eq)

data BoolIndex
  = ILess IntIndex IntIndex
  | ISLess IntIndex IntIndex
  | IEq IntIndex IntIndex
  | BNeg BoolIndex
  | IAnd BoolIndex BoolIndex
  | ITrue
  | IFalse
  deriving (Show,Eq)

data Sort
  = Subsort Ident Sort BoolIndex
  | IntSort
  | Pair Sort Sort
  | TypeSort
  deriving (Show,Eq)

data Exp =
    Var QualName
  | UnOp UnOp Exp -- when is this used
  | IfThenElse Exp Exp Exp
  | Apply Exp [Exp]
  | OpSection Operator -- why is it named OpSection
  | Lambda (Ident, Maybe TypeExp) (Maybe TypeExp) Exp
  | Index QualName Exp
  | IntLit Integer
  | FloatLit Double
  | BinOp Operator Exp Exp
  | Let [(Ident, Maybe TypeExp, Exp)] Exp 
  deriving Show

data Operator
  = Less
  | Times
  | Plus
  | Equals
  | Minus
  | Modulo
  | Divide
  deriving Show

data UnOp
  = Neg
  deriving Show

type Program = [Dec]

type Ident = String
type QualName = Ident