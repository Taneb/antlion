import Data.Integer as Integer
open Integer using (ℤ)

module NumberTheory.ModularArithmetic (m : ℤ) where

open import Algebra.Structures

open Integer hiding (+_; _-_) -- using (_+_; _*_; -_; +0)
open import Data.Integer.GCD
open import Data.Integer.Properties hiding (*-1-isMonoid; *-1-isCommutativeMonoid; +-*-isCommutativeRing)
open import Data.Integer.Tactic.RingSolver
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

_≈_ : Rel ℤ _
x ≈ y = ∃ λ k → k * m + x ≡ y

refl : Reflexive _≈_
refl {x} = +0 , (begin
  +0 * m + x
    ≡⟨ ≡.cong (_+ x) (*-zeroˡ m) ⟩
  +0 + x
    ≡⟨ +-identityˡ x ⟩
  x
    ∎)
  where
    open ≡.≡-Reasoning

sym : Symmetric _≈_
sym {x} {y} (k , p) = (- k) , (begin
  - k * m + y
    ≡˘⟨ ≡.cong₂ _+_ (neg-distribˡ-* k m) (neg-involutive y) ⟩
  - (k * m) + - - y
    ≡˘⟨ neg-distrib-+ (k * m) (- y) ⟩
  - (k * m + - y)
    ≡⟨ ≡.cong -_ (begin
      k * m + - y
        ≡˘⟨ +-identityʳ _ ⟩
      k * m + - y + +0
        ≡˘⟨ ≡.cong (k * m + - y +_) (+-inverseʳ x) ⟩
      k * m + - y + (x + - x)
        ≡˘⟨ +-assoc (k * m + - y) x (- x) ⟩
      k * m + - y + x + - x
        ≡⟨ ≡.cong (_+ - x) (begin
          k  * m + - y + x
            ≡⟨ +-assoc (k * m) (- y) x ⟩
          k * m + (- y + x)
            ≡⟨ ≡.cong (k * m +_) (+-comm (- y) x) ⟩
          k * m + (x + - y)
            ≡˘⟨ +-assoc (k * m) x (- y) ⟩
          k * m + x + - y
            ≡⟨ ≡.cong (_+ - y) p ⟩
          y + - y
            ≡⟨ +-inverseʳ y ⟩
          +0
            ∎) ⟩
      +0 + - x
        ≡⟨ +-identityˡ (- x) ⟩
      - x
        ∎) ⟩
  - - x
    ≡⟨ neg-involutive x ⟩
  x
    ∎)
  where
    open ≡.≡-Reasoning

trans : Transitive _≈_
trans {x} {y} {z} (j , p) (k , q) = k + j , (begin
  (k + j) * m + x
    ≡⟨ ≡.cong (_+ x) (*-distribʳ-+ (m) k j) ⟩
  k * m + j * m + x
    ≡⟨ +-assoc (k * m) (j * m) x ⟩
  k * m + (j * m + x)
    ≡⟨ ≡.cong (_+_ (k * m)) p ⟩
  k * m + y
    ≡⟨ q ⟩
  z
    ∎)
  where
    open ≡.≡-Reasoning

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

open IsEquivalence ≈-isEquivalence public using (reflexive)

setoid : Setoid _ _
setoid = record { isEquivalence = ≈-isEquivalence }

open import Algebra.Definitions _≈_

+-cong : Congruent₂ _+_
+-cong {x} {y} {u} {v} (j , p) (k , q) = j + k , (begin
  (j + k) * m + (x + u)
    ≡⟨ ≡.cong (_+ (x + u)) (*-distribʳ-+ m j k) ⟩
  j * m + k * m + (x + u)
    ≡˘⟨ +-assoc (j * m + k * m) x u ⟩
  j * m + k * m + x + u
    ≡⟨ ≡.cong (_+ u) (begin
    j * m + k * m + x
      ≡⟨ +-assoc (j * m) (k * m) x ⟩
    j * m + (k * m + x)
      ≡⟨ ≡.cong (j * m +_) (+-comm (k * m) x) ⟩
    j * m + (x + k * m)
      ≡˘⟨ +-assoc (j * m) x (k * m) ⟩
    j * m + x + k * m
      ∎) ⟩
  j * m + x + k * m + u
    ≡⟨ +-assoc (j * m + x) (k * m) u ⟩
  j * m + x + (k * m + u)
    ≡⟨ ≡.cong₂ _+_ p q ⟩
  y + v
    ∎)
  where
    open ≡.≡-Reasoning

*-cong : Congruent₂ _*_
*-cong {x} {y} {u} {v} (j , p) (k , q) = j * m * k + j * u + x * k , (begin
  (j * m * k + j * u + x * k) * m + x * u
    ≡⟨ ≡.cong (_+ x * u) (begin
    (j * m * k + j * u + x * k) * m
      ≡⟨ *-distribʳ-+ m (j * m * k + j * u) (x * k) ⟩
    (j * m * k + j * u) * m + (x * k) * m
      ≡⟨ ≡.cong₂ _+_ (*-distribʳ-+ m (j * m * k) (j * u)) (*-assoc x k m) ⟩
    j * m * k * m + j * u * m + x * (k * m)
      ≡⟨ ≡.cong (_+ x * (k * m)) (begin
      j * m * k * m + (j * u) * m
        ≡⟨ ≡.cong (_+ j * u * m) (*-assoc (j * m) k m) ⟩
      j * m * (k * m) + j * u * m
        ≡⟨ ≡.cong (j * m * (k * m) +_) (begin
        j * u * m
          ≡⟨ *-assoc j u m ⟩
        j * (u * m)
          ≡⟨ ≡.cong (j *_) (*-comm u m) ⟩
        j * (m * u)
          ≡˘⟨ *-assoc j m u ⟩
        j * m * u
          ∎) ⟩
      (j * m) * (k * m) + (j * m) * u
        ∎) ⟩
    j * m * (k * m) + j * m * u + x * (k * m)
      ∎) ⟩
  (j * m) * (k * m) + (j * m) * u + x * (k * m) + x * u
    ≡⟨ +-assoc ((j * m) * (k * m) + (j * m) * u) (x * (k * m)) (x * u) ⟩
  (j * m) * (k * m) + (j * m) * u + (x * (k * m) + x * u)
    ≡˘⟨ ≡.cong₂ _+_ (*-distribˡ-+ (j * m) (k * m) u) (*-distribˡ-+ x (k * m) u) ⟩
  (j * m) * (k * m + u) + x * (k * m + u)
    ≡˘⟨ *-distribʳ-+ (k * m + u) (j * m) x ⟩
  (j * m + x) * (k * m + u)
    ≡⟨ ≡.cong₂ _*_ p q ⟩
  y * v
    ∎)
  where
    open ≡.≡-Reasoning

neg-cong : Congruent₁ -_
neg-cong {x} {y} (k , p) = - k , (begin
  - k * m + - x
    ≡˘⟨ ≡.cong (_+ - x) (neg-distribˡ-* k m) ⟩
  - (k * m) + - x
    ≡˘⟨ neg-distrib-+ (k * m) x ⟩
  - (k * m + x)
    ≡⟨ ≡.cong -_ p ⟩
  - y
    ∎)
  where
    open ≡.≡-Reasoning

+-0-isAbelianGroup : IsAbelianGroup _≈_ _+_ +0 -_
+-0-isAbelianGroup = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≈-isEquivalence
          ; ∙-cong = +-cong
          }
        ; assoc = λ x y z → reflexive (+-assoc x y z)
        }
      ; identity = (λ x → reflexive (+-identityˡ x)) , λ x → reflexive (+-identityʳ x)
      }
    ; inverse = (λ x → reflexive (+-inverseˡ x)) , λ x → reflexive(+-inverseʳ x)
    ; ⁻¹-cong = neg-cong
    }
  ; comm = λ x y → reflexive (+-comm x y)
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≈_ _*_ (Integer.+ 1)
*-1-isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-isEquivalence
        ; ∙-cong = *-cong
        }
      ; assoc = λ x y z → reflexive (*-assoc x y z)
      }
    ; identity = (λ x → reflexive (*-identityˡ x)) , λ x → reflexive (*-identityʳ x )
    }
  ; comm = λ x y → reflexive (*-comm x y)
  }

open IsCommutativeMonoid *-1-isCommutativeMonoid using () renaming (isMonoid to *-1-isMonoid)

+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ +0 (Integer.+ 1)
+-*-isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = +-0-isAbelianGroup
    ; *-isMonoid = *-1-isMonoid
    ; distrib = (λ x y z → reflexive (*-distribˡ-+ x y z)) , λ x y z → reflexive (*-distribʳ-+ x y z)
    ; zero = (λ x → reflexive (*-zeroˡ x)) , λ x → reflexive (*-zeroʳ x)
    }
  ; *-comm = λ x y → reflexive (*-comm x y)
  }
