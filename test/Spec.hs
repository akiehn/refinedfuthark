
import Test.Tasty (defaultMain,TestTree,testGroup,TestName)
import Test.Tasty.HUnit
import RefinedFuthark.Parser
import RefinedFuthark.Syntax
-- import RefinedFuthark.Constraints
import RefinedFuthark.TypeCheck (typeCheck)

main :: IO ()
main =
  do 
     defaultMain $ testGroup "Tests" testGroups
  where testGroups = [testGroup "Parse Tests" parseTests,
                      --testGroup "Other Tests" otherTests,
                      testGroup "Type Tests" typeTests]

parseTests :: [TestTree]
parseTests =
  [testCase "Dummy Test" (return ())
  --,testCase "Another Dummy Test" $ 1+1 @?= 3
  ,testCase "parse empty file" $ assertParse "empty.fut" ""
  ,testCase "parse some white space" $ assertParse "whitespace.fut" "  "
  ,testCase "parse a let binding" $ assertParse "letbinding.fut" "let x : int32 = 5"
  ,testCase "parse float lit" $ assertParse "float.fut" "let x : f32 = 0.0"
  ,testCase "parse indexing" $ assertParse "letbinding.fut" "let x : int32 = x[5]"
  ,testCase "parse var" $ assertParse "letbinding.fut" "let x : int32 = x"
  ,testCase "parse type param" $ assertParse "letbinding.fut" "let x [n] : int32 = x"
  ,testCase "parse apply" $ assertParse "letbinding.fut" "let x : int32 = f y"
  ,testCase "parse lambda" $ assertParse "letbinding.fut" "let x : int32 = \\(x:i32) -> x"
  ,testCase "parse lambda ret type" $ assertParse "lambda.fut" "let x : int32 = \\(x:i32):i32 -> x"
  ,testCase "parse lambda map" $ assertParse "lambda.fut" "let x : int32 = map (\\(x:i32):i32 -> x) (iota 5)"
  ,testCase "parse apply 2" $ assertParse "letbinding.fut" "let x : int32 = let f = g x in f (3)"
  ,testCase "array type" $ assertParse "letbinding.fut" "let x : [n]i32 = x"
  ,testCase "multi array type" $ assertParse "letbinding.fut" "let x : [n][m]i32 = x"
  ,testCase "array type no index" $ assertParse "letbinding.fut" "let x : []i32 = x"
  ,testCase "parse apply" $ assertParse "apply.fut" "let x : int32 = f y"
  ,testCase "parse apply lit" $ assertParse "apply.fut" "let x : int32 = -x y"
  ,testCase "parse if then else" $ assertParse "ifthenelse.fut" "let x : int32 = if x then y else z"
  ,testCase "parse if then else 2" $ assertParse "ifthenelse.fut" "let x : int32 = if j < (m-1) then result[j+1] else 0.0"
  ,testCase "parse apply 2" $ assertParse "apply.fut" "let x : int32 = f (y z)"
  ,testCase "parse a let binding" $ assertParse "letbinding.fut" "let x : int32 = let y = 2 in y"
  ,testCase "parse adding numbers" $ assertParse "letbinding.fut" "let x : int32 = 2+2"
  ,testCase "parse subtract literals" $ assertParse "letbinding.fut" "let x : int32 = 2 - 2"
  ,testCase "parse subtract neg literals" $ assertExp "let x : int32 = -2 - 2" (\(BinOp Minus _ _) -> return ())
  ,testCase "parse subtract neg literals 2" $ assertParse "letbinding.fut" "let x : int32 = -2 - -2"
  ,testCase "parse subtract neg vars" $ assertParse "letbinding.fut" "let x : int32 = -x - -y"
  ,testCase "parse subtract numbers" $ assertExp "let x : int32 = 2 - 2" (\(BinOp Minus _ _) -> return ())
  ,testCase "parse app neg" $ assertExp "let x : int32 = f -2" (\(BinOp Minus _ _) -> return ())
  ,testCase "parse app neg 2" $ assertExp "let x : int32 = f -x" (\(BinOp Minus _ _) -> return ())
  ,testCase "parse app neg 3" $ assertExp "let x : int32 = f x -2" (\(BinOp Minus _ _) -> return ())
  ,testCase "parse app neg par" $ assertExp "let x : int32 = f (-2)" (\(Apply  _ _) -> return ())
  ,testCase "parse neglit" $ assertExp "let x : int32 = -2" (\(IntLit (-2)) -> return ())
  ,testCase "parse neg" $ assertExp "let x : int32 = -y" (\(UnOp Neg _) -> return ())
  ,testCase "parse neg app" $ assertExp "let x : int32 = -f x" (\(UnOp Neg _) -> return ())
  ,testCase "parse neg par" $ assertExp "let x : int32 = -(y)" (\(UnOp Neg _) -> return ())
  ,testCase "parse a let binding" $ assertParse "letbinding.fut" "let x : int32 = let y = 2 let z = 4 in y + z"
  ,testCase "parse a let binding" $ assertParse "letbinding.fut" "let x : int32 = let y = 2 let z = 4 in y + z let w : int32 = 1"
  ,testCase "parse a function" $ assertParse "letbinding.fut" "let f (x : int32) : int32 = x"
  ,testCase "parse a dependent function" $ assertParse "letbinding.fut" "let f (x : { i32(n) | n < 5 }) : i32 = x"
  ,testCase "parse indexing" $ assertParse "letbinding.fut" "let f [n] (x : i32) (arr : [n]i32) : int32 = arr[x]"
  ,testCase "parse a function 2" $ assertParse "letbinding.fut" "let foo 'a (x : a) : a = x"
  ,testCase "parse an array function" $ assertParse "letbinding.fut" "let foo 'a [n] (x : [n]a) : [n]a = x"
  ,testCase "parse an import" $ assertParse "import.fut" "import \"somefile\""
  ,testCase "parse map" $ assertParse "map.fut" "let x : y = map (\\(x:y) -> x) 2"
  ,testCase "parse fun type" $ assertParse "funtype.fut" "let x (f : i32 -> i32) : i32 -> i32 = f"
  ,testCase "parse fun lambda" $ assertParse "funtype.fut" "let x : i32 = map (\\x : (i32 -> i32) -> x)"
  ,testCase "parse segrep" $ assertParse "segrep.fut" "let replicated_iota [n] (arr : [n]i32) : []{i32(i) | 0 <= i && i < n} = undefined"
  ]

typeTests :: [TestTree]
typeTests =
  [
   testCheck "empty" ""
  ,testCheck "five" "let x : i32(5) = 5"
  ,negCheck "six" "let x : i32(5) = 6"
  ,testCheck "exfive" "let x : i32 = 5"
  ,testCheck "ints" "let x : [5]i32 = ints 5"
  ,testCheck "get2" "let y (x : {i32(a) | 0 <= a}): i32 = let z = x in get2 z"
  ,testCheck "get2" "let y : i32 = get2 5"
  ,testCheck "index" "let y : i32 = let x : [5]i32 = ints 5 in x[2]"
  -- ,testCheck "index2" "let y (z : {i32(k) | 0 <= k}): i32 = let arr = ints z let i : i32 = undefined in arr[i]"
  ,testCheck "index2" "let y [w] (arr : [w]i32) (j : {i32(h) | 0 <= h && h < w}): i32 = arr[j]"
  ,testCheck "iota" "let y [w] (z : i32(w)) (i : {i32(k) | 0 <= k && k < w}) : i32 = let arr = iota z let j = arr[i] let arr2 = ints z in arr2[j]"
  ,testCheck "mapIntId" "let y : [5]i32 = map idInt (ints 5)"
  ,testCheck "mapId" "let y : [5]i32 = map (\\x -> id x) (ints 5)"
  ,negCheck "mapIdNeg" "let y : [5]i32 = map (\\x -> id 5) (ints 5)"
  ,testCheck "mapget" "let y : [5]i32 = let vs = ints 5 in map (\\j -> vs[j]) (iota 5)"
  ,testCheck "mapIndex2" "let y : [5]i32 = let vs = ints 5 in map2 (iota 5) (\\j -> let jj = j in vs[jj])"
  ,testCheck "id 5" "let y : i32(5) = id 5"
  ,testCheck "id a" "let y (a : i32) : i32 = id a"
  ,testCheck "id id" "let y : i64 = let f = \\(x : i64) : i64 -> x in id f 1"
  ,testCheck "const" "let y (a : i32) : i32 = const a a"
  ,negCheck "negConst" "let y (a : i32) : i32 = const a 5"
  ,testCheck "segmented_replicate" "let segrep [n] (reps : [n]i32) (vs : [n]i32): []i32 = let idxs = rep_iota reps in map (\\i -> vs[i]) idxs"
  ]

-- testProg :: TestName -> String -> Constraint -> TestTree
-- testProg n s c = testCase n $ do
--   p <- tryParse "" s
--   c' <- tryCheck p
--   c' @?= c

testCheck :: TestName -> String -> TestTree
testCheck n s = testCase n $ do
  p <- tryParse "" s
  _ <- tryTypeCheck p
  return ()

negCheck :: TestName -> String -> TestTree
negCheck n s = testCase n $ do
  p <- tryParse "" s
  case typeCheck p of
    Right c -> assertFailure "Expected type checking failure"
    Left e -> return ()

tryTypeCheck :: Program -> Assertion
tryTypeCheck p = case typeCheck p of
  Left e -> assertFailure (show e)
  Right c -> return ()

-- testType :: TestName -> Exp -> TypeExp -> Constraint -> TestTree
-- testType n e t c = testCase n $ do
--   c' <- tryCheck [ValDec "_" [] [] t e]
--   c' @?= c

-- tryCheck :: Program -> IO Constraint
-- tryCheck p = case typeCheck p of
--   Left e -> assertFailure (show e)
--   Right c -> return c

assertExp :: String -> (Exp -> Assertion) -> Assertion
assertExp s f =
  case parseFile "" s of
    Right [ValDec _ _ _ _ e] -> f e
    Right _ -> assertFailure "Program has wrong shape"
    Left msg -> assertFailure (show msg)

assertParse :: String -> String -> Assertion
assertParse f s = tryParse f s >> return ()

tryParse :: SourceName -> String -> IO Program
tryParse fileName s =
  case parseFile fileName s of
    Right p -> return p
    Left e -> assertFailure (show e)

genConstraints :: String -> String -> Assertion
genConstraints f s = case typeCheck <$> parseFile f s of
  Right (Right _) -> return ()
  Left e -> assertFailure (show e)
  Right (Left e) -> assertFailure (show e)


makeTest :: String -> TestTree
makeTest f = testCase f (readFile f >>= assertParse f)
