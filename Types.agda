module Types where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)

-- Universe for non-linear types
data U : Set where
  Uℕ    : ℕ → U
  UBool : Bool → U

data LType : Set where
  One   : LType
  _⊸_   : LType → LType → LType -- Lolli
  _⊗_   : LType → LType → LType -- Tensor
  _⊕_   : LType → LType → LType -- Plus
  _&_   : LType → LType → LType -- With
  Lower : U     → LType

infixr 0 _⊸_
infixr 3 _⊗_ _⊕_ _&_

Ident = ℕ

data Usage : Set where
  used   : LType → Usage
  unused : Usage

data NCtx : Set where
  end  : LType → NCtx
  cons : Usage → NCtx → NCtx

data Ctx : Set where
  empty    : Ctx
  nonEmpty : NCtx → Ctx

-- ??? This is new.
-- Constructs an NCtx with the type at the end preceeded by all unused.
newN : Ident → LType → NCtx
newN zero s    = end s
newN (suc x) s = cons unused (newN x s)

-- ??? What happens when we try to add a type that already exists?
-- For now I overwrite.
addNN : Ident → LType → NCtx → NCtx
addNN zero    s (end _)    = end s                    -- replace
addNN (suc x) s (end t)    = cons (used t) (newN x s) -- add to the end, padding as necessary
addNN zero    s (cons _ g) = cons (used s) g          -- replace if used
addNN (suc x) s (cons u g) = cons u (addNN x s g)

addN : Ident → LType → Ctx → NCtx
addN zero    s empty        = end s
addN (suc x) s empty        = cons unused (addN x s empty)
addN x       s (nonEmpty g) = addNN x s g

add : Ident → LType → Ctx → Ctx
add x s g = nonEmpty (addN x s g)
