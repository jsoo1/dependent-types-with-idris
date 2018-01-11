module Main


-- main : IO ()
-- main = putStrLn ?greeting


-- data (=) : a -> b -> Type where
--      Refl : x = x


mult : Nat -> Nat -> Nat
mult Z     y = Z
mult (S k) y = plus y (Main.mult k y)


reverse : List a -> List a
reverse xs = revAcc [] xs where
    revAcc : List a -> List a -> List a
    revAcc acc [] = acc
    revAcc acc (x :: xs) = revAcc (x :: acc) xs


-- even : Nat -> Bool
-- even Z = True
-- even (S k) = ?even_rhs


isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat


data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a



-- data FizzBuzzType = Fizz | Buzz | FizzBuzz | Nope Int


-- fizzBuzz : Nat -> FizzBuzzType
-- fizzBuzz x = case x of
--          (mod 15 x = 0) => FizzBuzz
--          (mod 3 x = 0) => Fizz
--          (mod 5 x = 0) => Buzz
--          _ = Nope


(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys


-- data InterviewQuestion : (n : Nat) -> Type where
--      Fizz : InterviewQuestion (n * 3)
--      Buzz : InterviewQuestion (n * 5)
--      FizzBuzz : InterviewQuestion (n * 15)


-- fizzBuzz : InterviewQuestion -> IO ()
-- fizzBuzz x = case x of
--          Fizz => putStrLn "fizz"
--          Buzz => putStrLn "buzz"
--          FizzBuzz => putStrLn "fizzbuzz"


data Parity : Nat -> Type where
     Even : Parity (n + n)
     Odd : Parity (S (n + n))


helpEven : (j : Nat) -> Parity (S j + S j) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p


helpOdd : (j : Nat) -> Parity (S (S (j + S j))) -> Parity (S (S (S (plus j j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p


parity : (n : Nat) -> Parity n
parity Z = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
       parity (S (S (j + j)))     | Even = helpEven j (Even {n = S j})
          -- let result = Even {n=S j} in ?helpEven
       parity (S (S (S (j + j)))) | Odd  = helpOdd j (Odd {n = S j})
          -- let result = Odd {n=S j} in ?helpOdd


natToBin : Nat -> List Bool
natToBin Z = Nil
natToBin k with (parity k)
         natToBin (j + j)     | Even = False :: natToBin j
         natToBin (S (j + j)) | Odd  = True  :: natToBin j


-- data FB : Nat -> Type where
--      FizzBuzz : FB (n * 15)
--      Fizz : FB (n * 3)
--      Buzz : FB (n * 5)

data FB {n=Nat} : fizzbuzz n -> Type where
     
