module Utils where

open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

_-_ : ℕ → ℕ → ℕ
m - zero = m
m - suc n = pred (m - n)

≤cases : ∀{n m} → n ≤ m → n ≡ m ⊎ n < m
≤cases {m = zero} z≤n = inj₁ refl
≤cases {m = suc m} z≤n = inj₂ (s≤s z≤n)
≤cases (s≤s p) with ≤cases p
≤cases (s≤s p) | inj₁ x = inj₁ (cong suc x)
≤cases (s≤s p) | inj₂ y = inj₂ (s≤s y)

qwerty : ∀ m n → ¬ m ≤ n → m > n
qwerty zero zero p = ⊥-elim (p z≤n)
qwerty zero (suc n) p = ⊥-elim (p z≤n)
qwerty (suc m) zero p = s≤s z≤n
qwerty (suc m) (suc n) p = s≤s (qwerty m n (λ z → p (s≤s z)))

same≤ : ∀{x y} → (p q : x ≤ y) → p ≡ q
same≤ z≤n z≤n = refl
same≤ (s≤s p) (s≤s q) = cong s≤s (same≤ p q)

plus-succ : ∀ x y → x + suc y ≡ suc (x + y)
plus-succ zero y = refl
plus-succ (suc x) y = cong suc (plus-succ x y)

plus-0 : ∀ x → x + 0 ≡ x
plus-0 zero = refl
plus-0 (suc x) = cong suc (plus-0 x)

plus-comm : ∀ x y → x + y ≡ y + x
plus-comm zero y = sym (plus-0 y)
plus-comm (suc x) zero = cong suc (plus-comm x zero)
plus-comm (suc x) (suc y) =
  trans (cong suc (plus-succ x y)) (cong suc (plus-comm (suc x) y))

≤refl : ∀ x → x ≤ x
≤refl zero = z≤n
≤refl (suc x) = s≤s (≤refl x)

≤succ : ∀ {x y} → x ≤ y → x ≤ suc y
≤succ z≤n = z≤n
≤succ (s≤s p) = s≤s (≤succ p)

>succ : ∀ {n m} → n > m → suc n > m
>succ (s≤s p) = s≤s (≤succ p)

≤trans : ∀{p q r} → p ≤ q → q ≤ r → p ≤ r
≤trans z≤n z≤n = z≤n
≤trans z≤n (s≤s q) = z≤n
≤trans (s≤s p) (s≤s q) = s≤s (≤trans p q)

absurd-suc : ∀{n} → suc n ≤ n → ⊥
absurd-suc (s≤s p) = absurd-suc p
