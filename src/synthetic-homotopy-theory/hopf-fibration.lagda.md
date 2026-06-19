# The Hopf fibration

```agda
module synthetic-homotopy-theory.hopf-fibration where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.path-algebra
open import foundation.transport-along-higher-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
open import foundation.whiskering-identifications-concatenation
open import foundation.equivalences
open import foundation.function-types

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.triple-loop-spaces
open import synthetic-homotopy-theory.eckmann-hilton-argument

open import synthetic-homotopy-theory.universal-property-two-sphere
open import synthetic-homotopy-theory.universal-property-three-sphere
open import synthetic-homotopy-theory.free-two-loops
open import synthetic-homotopy-theory.free-three-loops

open import synthetic-homotopy-theory.two-sphere
open import synthetic-homotopy-theory.three-sphere
open import synthetic-homotopy-theory.circle
open import foundation-core.fibers-of-maps
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.whiskering-homotopies-composition
open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea


## Definitions

### Generating three loop of the two sphere

```agda
module _
  (up-𝕊² : universal-property-two-sphere free-two-loop-𝕊²) (up-𝕊³ : universal-property-three-sphere free-three-loop-𝕊³)
  where

  hopf-fibration : 𝕊³ → 𝕊²
  hopf-fibration = map-inv-equiv (equiv-universal-property-𝕊³ up-𝕊³ 𝕊²) free-3-loop-eckmann-hilton-𝕊²

  hopf-fibration-algebra :
    (l1 : Level) → UU (lsuc l1)
  hopf-fibration-algebra l1 =
    Σ (UU l1)
      λ X → Σ X
        λ x →
          Σ (id {A = X} ~ id)
            λ H →
              nat-htpy-id~id H (H x) ＝ refl

  type-hopf-fibration-algebra :
    {l1 : Level} → hopf-fibration-algebra l1 → UU l1
  type-hopf-fibration-algebra = pr1

  point-hopf-fibration-algebra :
    {l1 : Level} → (X : hopf-fibration-algebra l1) → type-hopf-fibration-algebra X
  point-hopf-fibration-algebra = pr1 ∘ pr2

  two-automorphism-hopf-fibration-algebra :
    {l1 : Level} → (X : hopf-fibration-algebra l1) → id {A = type-hopf-fibration-algebra X} ~ id
  two-automorphism-hopf-fibration-algebra = pr1 ∘ pr2 ∘ pr2
  
  hopf-fibration-algebra-morphism :
    {l1 l2 : Level} (X : hopf-fibration-algebra l1) (Y : hopf-fibration-algebra l2) → UU (l1 ⊔ l2)
  hopf-fibration-algebra-morphism X Y =
    Σ (type-hopf-fibration-algebra X → type-hopf-fibration-algebra Y)
      λ f →
        Σ (f (point-hopf-fibration-algebra X) ＝ point-hopf-fibration-algebra Y)
          λ p →
            Σ (f ·l (two-automorphism-hopf-fibration-algebra X) ~ (two-automorphism-hopf-fibration-algebra Y) ·r f)
              λ H →
                {!!}


  hopf-fibration-algebra-𝕊¹ : hopf-fibration-algebra lzero
  pr1 hopf-fibration-algebra-𝕊¹ = 𝕊¹
  pr1 (pr2 hopf-fibration-algebra-𝕊¹) = base-𝕊¹
  pr1 (pr2 (pr2 hopf-fibration-algebra-𝕊¹)) = 2-automorphisms-𝕊¹
  pr2 (pr2 (pr2 hopf-fibration-algebra-𝕊¹)) = {!!}

  universal-property-family-of-fibers-of-hopf-fibration : UUω
  universal-property-family-of-fibers-of-hopf-fibration =
    {!!}

  something :
    {l1 : Level} (P : 𝕊² → UU l1) → {!!} ≃ lift-family-of-elements P hopf-fibration
  something = {!!}
  
  compute-fiber-over-base-hopf-fibration : 𝕊¹ ≃ fiber hopf-fibration base-𝕊²
  compute-fiber-over-base-hopf-fibration = {!!}
```

