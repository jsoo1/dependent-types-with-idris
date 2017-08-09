module FizzBuzz


infixl 1 |>
(|>) : a -> (a -> b) -> b
x |> f = f x


data Fin : Nat -> Type where
     FZ : (k:Nat) -> Fin (S k)
     FS : (k:Nat) -> Fin k -> Fin (S k)


Show (Fin n) where
  show (FZ k) = "FZ " ++ show k
  show (FS k x) = "FS " ++ show k ++ show x


record Product (n:Nat) (m:Nat) ((n * m):Nat)where
       constructor Mult


-- codata Multiples : (n:Nat) -> Type where
--        (::) : Product
--             -> initial * factor
--             -> Multiples n
