module Permissions where
open import IO.Primitive using (IO; readFile; writeFile; _>>=_; return)
open import Data.String using (String)
open import Codata.Musical.Costring using (Costring)
open import Foreign.Haskell using (Unit)
open import Level

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

-- checkT : Set -> Key -> Set
-- checkT t Good = t
-- checkT _ _ = Fail

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x


rawIMonad : RawIMonad (λ i j A → i ∈ M (const A ∩ ｛ j ｝))
  rawIMonad = record
    { return = λ x → return? (x , refl); 
      _>>=_  = λ m k → m ?>= λ { {._} (x , refl) → k x }
      
    }

data FS { ℓ : Level } (a : Set ℓ) : Set (suc ℓ) where
  Read  : Fd -> FS a
  Write : Fd -> Content -> FS a
  _>>>=_  : ∀ {ℓ'} {b : Set ℓ'} -> FS b -> (b -> FS a) -> FS {ℓ ⊔ ℓ'} a
  ret   : a -> FS a

infixr 15 _>>>=_


-- run : forall {a} -> (k : Key) -> FS a -> IO (checkT a k)
-- run Good (Read fn) = readFile fn
-- run Good (Write fn s) = writeFile fn s
-- run Good (b >>>= c) = run Good b >>= (\x -> run Good (c x))
-- run Good (ret x) = return x
-- run Bad  _ = return fail

-- main : IO Unit
-- main = let k = Good in
--        run k (Read >>>= ret)

