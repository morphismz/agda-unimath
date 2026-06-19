# Free two loops

```agda
module synthetic-homotopy-theory.free-two-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.whiskering-identifications-concatenation
open import foundation-core.commuting-squares-of-identifications 
open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.dependent-double-loop-spaces
open import synthetic-homotopy-theory.double-loop-spaces
open import foundation-core.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.transport-along-higher-identifications
open import foundation.action-on-identifications-dependent-functions
open import foundation.homotopies
```

</details>

## Idea

## Definitions

### Free two loops

```agda
free-two-loop : {l1 : Level} (X : UU l1) → UU l1
free-two-loop X = Σ X (λ x → type-Ω² x)

module _
  {l1 : Level} {X : UU l1}
  where

  base-free-two-loop : free-two-loop X → X
  base-free-two-loop = pr1

  two-loop-free-loop : (α : free-two-loop X) → type-Ω² (base-free-two-loop α)
  two-loop-free-loop = pr2
```

### Free dependent two loops

```agda
free-dependent-two-loop : {l1 l2 : Level} {X : UU l1} (B : X → UU l2) (α : free-two-loop X) → UU l2
free-dependent-two-loop B α =
  Σ ( B (base-free-two-loop α)) (dependent-Ω² B (two-loop-free-loop α))

module _
  {l1 l2 : Level} {X : UU l1} (B : X → UU l2) (α : free-two-loop X)
  where

  base-free-dependent-two-loop : free-dependent-two-loop B α → B (base-free-two-loop α)
  base-free-dependent-two-loop = pr1

  two-loop-free-dependent-loop : (s : free-dependent-two-loop B α) → dependent-Ω² B (two-loop-free-loop α) (base-free-dependent-two-loop s)
  two-loop-free-dependent-loop = pr2
```

## Properties

### Characterization of the identity type of the type of free two loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  Eq-free-two-loop : (α α' : free-two-loop X) → UU l1
  Eq-free-two-loop α α' =
    Σ (base-free-two-loop α ＝ base-free-two-loop α')
      ( λ p →
        coherence-square-identifications
          (inv right-unit)
          (right-whisker-concat (two-loop-free-loop α)  p)
          (left-whisker-concat p (two-loop-free-loop α'))
          (inv right-unit))

  refl-Eq-free-two-loop : (α : free-two-loop X) → Eq-free-two-loop α α
  pr1 (refl-Eq-free-two-loop α) = refl
  pr2 (refl-Eq-free-two-loop α) =
    right-unit ∙
    right-unit-law-right-whisker-Ω² (two-loop-free-loop α) ∙
    inv (left-unit-law-left-whisker-Ω² (two-loop-free-loop α))

  Eq-eq-free-two-loop : (α α' : free-two-loop X) → α ＝ α' → Eq-free-two-loop α α'
  Eq-eq-free-two-loop α .α refl = refl-Eq-free-two-loop α

  abstract
    is-torsorial-Eq-free-two-loop :
      (α : free-two-loop X) → is-torsorial (Eq-free-two-loop α)
    is-torsorial-Eq-free-two-loop α =
      is-torsorial-Eq-structure
        (is-torsorial-Id (base-free-two-loop α))
        (base-free-two-loop α , refl)
        (is-contr-is-equiv'
          (Σ (type-Ω² (base-free-two-loop α)) (λ α' → two-loop-free-loop α ＝ α'))
          (tot
            (λ α' p →
              right-unit ∙
              right-unit-law-right-whisker-Ω² (two-loop-free-loop α) ∙
              p ∙
              inv (left-unit-law-left-whisker-Ω² α')))
          (is-equiv-tot-is-fiberwise-equiv
            λ α' →
              is-equiv-comp
                (concat'
                  ((right-whisker-concat (two-loop-free-loop α) refl) ∙ refl)
                  (inv (left-unit-law-left-whisker-Ω² α')))
                (concat
                  (right-unit ∙ right-unit-law-right-whisker-Ω² (pr2 α)) α')
                (is-equiv-concat (right-unit ∙ right-unit-law-right-whisker-Ω² (pr2 α)) α')
                (is-equiv-concat'
                  ((right-whisker-concat (two-loop-free-loop α) refl) ∙ refl)
                  (inv (left-unit-law-left-whisker-Ω² α'))))
          (is-torsorial-Id (two-loop-free-loop α)))

  abstract
    is-equiv-Eq-eq-free-two-loop :
      (α α' : free-two-loop X) → is-equiv (Eq-eq-free-two-loop α α')
    is-equiv-Eq-eq-free-two-loop α = fundamental-theorem-id (is-torsorial-Eq-free-two-loop α) (Eq-eq-free-two-loop α)
```

### Characterization of the identity type of the type of free dependent two loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (B : X → UU l2) (α : free-two-loop X)
  where

  Eq-free-dependent-two-loop : (s s' : free-dependent-two-loop B α) → UU l2
  Eq-free-dependent-two-loop s s' =
    Σ ( base-free-dependent-two-loop B α s ＝ base-free-dependent-two-loop B α s')
      ( λ p →
        coherence-square-identifications
          (nat-htpy-id~id (tr² B (two-loop-free-loop α)) p)
          (right-whisker-concat (two-loop-free-dependent-loop B α s) p)
          (left-whisker-concat p (two-loop-free-dependent-loop B α s'))
          (inv right-unit))
```
