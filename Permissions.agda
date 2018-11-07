module Permissions where
open import IO.Primitive using (IO; readFile; writeFile; _>>=_; return)
open import Data.String using (String)
open import Codata.Musical.Costring using (Costring)
open import Foreign.Haskell using (Unit)

data Key : Set where
    Good : Key
    Bad : Key

Fd : Set
Fd = String

Content : Set
Content = Costring

data Fail : Set where
  fail : Fail

data Empty : Set where

checkT : Set -> Key -> Set
checkT t Good = t
checkT _ _ = Fail

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

data FS {a : Set} : Set -> Set where
  Read  : Fd -> FS Content
  Write : Fd -> Content -> FS Unit
  _>=_  : forall {b} -> FS a -> (a -> FS b) -> FS b
  ret   : forall {b} -> b -> FS b

infixr 15 _>=_

run : forall {a} -> (k : Key) -> FS a -> IO (checkT a k)
run Good (Read fn) = readFile fn
run Good (Write fn s) = writeFile fn s
run Good (b >= c) = run Good b >>= (\x -> run Good (c x))
run Good (ret x) = return x
run Bad  _ = return fail

-- main : IO Unit
-- main = let k = Good in
--        run k (Read >= ret)

