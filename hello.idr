module Main


main : IO ()
main = putStrLn "Hello world"


isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat


mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []


data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a


(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys


data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)


index : Fin n -> Vect n a -> a
index FZ (x :: xs) = x
index (FS k) (x :: xs) = index k xs


tlv : Vect 3 Char
tlv = ['t', 'l', 'v']


using (x:a, y:a, xs:Vect n a)
  data IsElem : a -> Vect n a -> Type where
    Here : IsElem x (x :: xs)
    There : IsElem x xs -> IsElem x (y :: xs)


inTLV : IsElem 'v' Main.tlv
inTLV = There (There (Here))


mutual
  even
