module New


data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k ) a


(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil        ys = ys
(++) (x :: xs)  ys = x :: xs ++ ys


data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)


index : (i:Fin n) -> (xs:Vect n a) -> a
index FZ      (x :: xs) = x
index (FS k)  (x :: xs) = index k xs


isEmpty : Vect n a -> Bool
isEmpty {n = Z} _     = True
isEmpty {n = S k} _   = False


using (x:a, y:a, xs:Vect n a)
  data IsElem : a -> Vect n a -> Type where
      Here :   IsElem x (x :: xs)
      There :  IsElem x xs -> IsElem x (y :: xs)


testVec : Vect 4 Int
testVec = 3 :: 4 :: 5 :: 6 :: Nil


inVect : IsElem 5 New.testVec
inVect = There (There Here)


mod3 : Nat -> Nat
mod3 n = mod n 3


-- divisible_by_three : (n : Nat) -> mod3 (n)
-- divisible_by_three {n = Z} = ?helpDiv3_1
-- divisible_by_three {n = (S k)} = ?helpDiv3_2


-- data FB : Nat -> Nat -> Type where
--      FizzBuzz : 15 =>


-- using (n:Nat)
--   data FB : Nat -> Type where
--       FizzBuzz : (n * 15) -> FB (n - 1)
--       Buzz : (n * 5) -> FB (n - 1)
--       Fizz : (n * 3) -> FB (n -1)


plus_commutes_rhs_Z : m = plus m 0
plus_commutes_rhs_Z {m = Z} = Refl
plus_commutes_rhs_Z {m = (S k)} = let rec = plus_commutes_rhs_Z {m = k} in
                                      rewrite sym rec in Refl


plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_S k Z = Refl
plus_commutes_S k (S j) = rewrite plus_commutes_S k j in Refl


total
plus_commutes : (n,m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_rhs_Z
plus_commutes (S k) m = rewrite plus_commutes k m in (plus_commutes_S k m)
