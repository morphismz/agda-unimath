```agda
module synthetic-homotopy-theory.three-sphere where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.action-on-higher-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-two-loops
open import synthetic-homotopy-theory.dependent-double-loop-spaces

open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.triple-loop-spaces
open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.universal-property-two-sphere

open import synthetic-homotopy-theory.spheres

open import structured-types.pointed-types

open import synthetic-homotopy-theory.free-three-loops
open import synthetic-homotopy-theory.circle
open import structured-types.pointed-equivalences
open import univalent-combinatorics.standard-finite-types
open import synthetic-homotopy-theory.two-sphere

open import synthetic-homotopy-theory.universal-property-three-sphere
```

</details>

## Definitions

### The standard three sphere

```agda
𝕊³-Pointed-Type : Pointed-Type lzero
𝕊³-Pointed-Type = sphere-Pointed-Type 3

𝕊³ : UU lzero
𝕊³ = type-Pointed-Type 𝕊³-Pointed-Type

base-𝕊³ : 𝕊³
base-𝕊³ = point-Pointed-Type 𝕊³-Pointed-Type

three-loop-𝕊³ : type-Ω³ base-𝕊³
three-loop-𝕊³ =
  map-pointed-equiv
    (pointed-equiv-3-loop-pointed-identity 𝕊³-Pointed-Type (meridian-sphere 2 base-𝕊²))
    (ap² (meridian-sphere 2) two-loop-𝕊²)

free-three-loop-𝕊³ : free-three-loop 𝕊³
pr1 free-three-loop-𝕊³ = base-𝕊³
pr2 free-three-loop-𝕊³ = three-loop-𝕊³

module _
  (up : universal-property-three-sphere free-three-loop-𝕊³)
  where

  universal-property-𝕊³ : universal-property-three-sphere free-three-loop-𝕊³
  universal-property-𝕊³ = up

  equiv-universal-property-𝕊³ :
    {l : Level} (X : UU l) → (𝕊³ → X) ≃ free-three-loop X
  pr1 (equiv-universal-property-𝕊³ X) = ev-free-three-loop free-three-loop-𝕊³ X
  pr2 (equiv-universal-property-𝕊³ X) = universal-property-𝕊³ X

module _
  (up : dependent-universal-property-three-sphere free-three-loop-𝕊³)
  where

  dependent-universal-property-𝕊³ : dependent-universal-property-three-sphere free-three-loop-𝕊³
  dependent-universal-property-𝕊³ = up

  equiv-dependent-universal-property-𝕊³ :
    {l : Level} (P : 𝕊³ →  UU l) → ((x : 𝕊³) → P x) ≃ free-dependent-three-loop P free-three-loop-𝕊³
  pr1 (equiv-dependent-universal-property-𝕊³ P) = ev-free-three-loop-Π free-three-loop-𝕊³ P
  pr2 (equiv-dependent-universal-property-𝕊³ P) = dependent-universal-property-𝕊³ P
```
