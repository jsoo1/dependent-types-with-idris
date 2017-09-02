module FizzBuzz


infixl 1 |>
(|>) : a -> (a -> b) -> b
x |> f = f x





codata FB : Nat -> Type where
     Fizz :











-- Show (Fin n) where
--   show (FZ k) = "FZ " ++ show k
--   show (FS k x) = "FS " ++ show k ++ show x


-- fizzbuzz : Nat -> Nat
-- fizzbuzz n = case (mod n 15, mod n 5, mod n 3) of
--          (Z,_,_) => n + 2
--          (_,Z,_) => n + 2
--          (_,_,Z) => n + 2

-- data FB : Nat -> Type where
--      Job : FB Z
--      Fizz : Inf FB (fizzbuzz n) -> FB n
--      Buzz : Inf FB (fizzbuzz n) -> FB n
--      FizzBuzz : Inf FB (fizzbuzz n) -> FB n


-- -- record Product (n:Nat) where
-- --        constructor Mult
-- --        a: Nat
-- --        b: Nat


-- -- codata Multiples : (n:Nat) -> Type where
-- --        (::) : Product n m
-- --             -> Product n (Mult n (S m))
-- --             -> Multiples n
