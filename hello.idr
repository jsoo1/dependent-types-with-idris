module Main


main : IO ()
main = do
  putStr "Hi, type some shit...\n> "
  str <- getLine
  putStrLn str


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
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k


printIt : String -> IO ()
printIt x = putStrLn x


aVal : Nat
aVal = 7


aVect : Vect Main.aVal Int
aVect = 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: Nil


data DPair : (a : Type) -> (P : a -> Type) -> Type where
     MkDPair : {P : a -> Type} -> (x : a) -> P x -> Main.DPair a P


myDPair : Main.DPair Nat (\n => Vect n Int)
myDPair = MkDPair 2 [0, 1]


notherVec : (n : Nat ** Vect n Int)
notherVec = (_ ** [3, 4])


filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter p Nil = (_ ** [])
filter p (x :: xs) with (filter p xs)
  | (_ ** xs') = if (p x) then (_ ** x :: xs') else (_ ** xs')
