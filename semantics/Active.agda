module Active where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Rational
open import Relation.Binary.PropositionalEquality

module ℚ-misc where
  open import Data.Integer as ℤ using (+_)
  open import Relation.Nullary.Decidable
  open import Data.Nat.Coprimality as C

  toℚ : ℕ → ℚ
  toℚ n = {!!}
    -- not sure why this doesn't work
    -- (+ n ÷ 1) { fromWitness (C.sym (1-coprimeTo n)) } { tt }

  -- forget it, just use ℕ as type of durations for now

Dur : Set
Dur = ℕ

data SpliceType : Set where
  L  : SpliceType
  R  : SpliceType
  LR : SpliceType

End : (A : Set) → Set
End A = A × SpliceType

agreeR : {A : Set} → End A → (Dur → A) → Set
agreeR (_ , L) f = ⊤
agreeR (a , _) f = f 0 ≡ a

agreeL : {A : Set} → Dur → End A → (Dur → A) → Set
agreeL d (_ , R) f = ⊤
agreeL d (a , _) f = f d ≡ a

Animation : {A : Set} → End A → Dur → End A → Set
Animation {A} a₁ d a₂ = Σ[ f ∈ (Dur → A) ] (agreeR a₁ f × agreeL d a₂ f)

splice : {A : Set} → (Dur → A) → Dur → SpliceType → (Dur → A) → Dur → A
splice f₁ d L f₂ d′ = {!!}
splice f₁ d R f₂ d′ = {!!}
splice f₁ d LR f₂ d′ = {!!}

_↔_ : {A : Set} {a₁ a₂ a₃ : End A} {d₁ d₂ : Dur} → Animation a₁ d₁ a₂ → Animation a₂ d₂ a₃ → Animation a₁ (d₁ + d₂) a₃
_↔_ {_} {a₁ , s₁} {a₂ , s₂} {a₃ , s₃} {d₁} (f₁ , agree₁) (f₂ , agree₂) = splice f₁ d₁ s₂ f₂ , {!!}
