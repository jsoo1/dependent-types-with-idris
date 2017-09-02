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


record Person where
       constructor MkPerson
       firstName, middleName, lastName : String
       age : Int


fred : Person
fred = MkPerson "Fred" "Joe" "Bloggs" 30


fredsBrother : Person
fredsBrother = record { firstName = "John", lastName $= id, age $= (*2) } fred


record Class where
       constructor ClassInfo
       students : Vect n Person
       className : String
       teacher : Person


addStudent : Person -> Class -> Class
addStudent p c = record { students = p ::  students c } c


addStudent' : Person -> Class -> Class
addStudent' p c = record { students $= (p ::) } c


professorX : Person
professorX = MkPerson "Prof" "Y" "X" 38


csClass : Class
csClass = ClassInfo [fred, fredsBrother] "CS" professorX


record Prod a b where
       constructor Times
       fst : a
       snd : b


spaceIsh : Prod Double Double
spaceIsh = Times 4 69.420


record SizedClass (size : Nat) where
       constructor SizedClassInfo
       students : Vect size Person
       className : String


csDesc : SizedClass 2
csDesc = SizedClassInfo [fred, fredsBrother] "CS"


dAddStudent : Person -> SizedClass n -> SizedClass (S n)
dAddStudent p c = SizedClassInfo (p :: students c ) (className c)


mirror : List a -> List a
mirror xs = let xs' = reverse xs in
                xs ++ xs'


showPerson : Person -> String
showPerson p = let MkPerson firstName middleName lastName age = p in
                   firstName ++ " " ++ middleName ++ " " ++ lastName ++ " is " ++ show age ++ " years old"


interface Show a where
          show : a -> String


Main.Show Nat where
     show Z = "Z"
     show (S k) = "S" ++ Main.show k


Main.Show a => Main.Show (Vect n a) where
     show xs = "[" ++ show' xs ++ "]" where
          show' : Vect n a -> String
          show' Nil        = ""
          show' (x :: Nil) = show x
          show' (x :: xs)  = Main.show x ++ ", " ++ show' xs


aVect2 : Vect 5 Nat
aVect2 = [10, 9, 0, 1, 100]


data Ordering = LT | EQ | GT


interface Eq a => Ord a where
          compare : a -> a -> Main.Ordering

          (<) : a -> a -> Bool
          (>) : a -> a -> Bool
          (<=) : a -> a -> Bool
          (>=) : a -> a -> Bool
          max : a -> a -> a
          min : a -> a -> a


sortAndShow : (Prelude.Interfaces.Ord a, Prelude.Show.Show a) => List a -> String
sortAndShow xs = show (sort xs)


interface Functor (f : Type -> Type) where
          map : (m : a -> b) -> f a -> f b


Main.Functor List where
        map f [] = []
        map f (x::xs) = f x :: Main.map f xs


infixl 2 <*>
interface Main.Functor f => Main.Applicative (f : Type -> Type) where
          pure : a -> f a
          (<*>) : f (a -> b) -> f a -> f b


infixl 0 |>
(|>) : a -> (a -> b) -> b
(|>) x f = f x


interface Main.Applicative m => Main.Monad (m : Type -> Type) where
          (>>=) : m a -> (a -> m b) -> m b


Main.Functor Maybe where
             map _ Nothing = Nothing
             map f (Just x) = Just (f x)


-- Main.Applicative Maybe where
--                  pure x = Just x
--                  Nothing <*> _ = Nothing
--                  _ <*> Nothing = Nothing
--                  (Just f) <*> (Just x) = Just (f x)


-- Main.Monad Maybe where
--       Nothing >>= k = Nothing
--       (Just x) >>= k = k x


m_add : Maybe Int -> Maybe Int -> Maybe Int
m_add x y = do
      x' <- x
      y' <- y
      pure (x' + y')


fve : isSingleton True
fve = 5


fveList : isSingleton False
fveList = [5, 5, 5, 5, 5, 5]


mkSingle
