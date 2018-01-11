module FizzBuzz


-- fizzbuzz : Nat -> Nat
-- fizzbuzz n =


-- data FB : Nat -> Type where
--   Nil : FB 0


-- Idiom brackets applied to Evaluators
data Expr = Var String
     | Val Int
     | Add Expr Expr


data Eval : Type -> Type where
     MkEval : (List (String, Int) -> Maybe a) -> Eval a


fetch : String -> Eval Int
fetch x = MkEval (\e => fetchVal e) where
      fetchVal : List (String, Int) -> Maybe Int
      fetchVal [] = Nothing
      fetchVal ((v, val) :: xs) =
               if (x == v)
               then (Just val)
               else (fetchVal xs)


Functor Eval where
        map f (MkEval g) = MkEval (\e => map f (g e))


Applicative Eval where
            pure x = MkEval (\e => Just x)
            (<*>) (MkEval f) (MkEval g) = MkEval (\x => app (f x) (g x)) where
                  app : Maybe (a -> b) -> Maybe a -> Maybe b
                  app (Just fx) (Just gx) = Just (fx gx)
                  app _         _         = Nothing


eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val x) = [| x |]
eval (Add x y) = [| eval x + eval y |]


runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e = case eval e of
        MkEval envFn => envFn env


-- Named implementations
[myord] Ord Nat where
        compare Z (S n) = GT
        compare (S n) Z = LT
        compare Z Z     = EQ
        compare (S x) (S y) = compare @{myord} x y


testList : List Nat
testList = [3, 4, 1]


interface Semigroup ty where
          (<+>) : ty -> ty -> ty


interface FizzBuzz.Semigroup ty => Monoid ty where
          neutral : ty


[PlusNatSemi] FizzBuzz.Semigroup Nat where
              (<+>) x y = x + y


[MultNatSemi] FizzBuzz.Semigroup Nat where
              (<+>) x y = x * y


[PlusNatMonoid] FizzBuzz.Monoid Nat using PlusNatSemi where
                neutral = 0


[MultNatMonoid] FizzBuzz.Monoid Nat using MultNatSemi where
                neutral = 1


-- Determining Parameters
interface Monad m => MonadState s (m : Type -> Type) | m where





