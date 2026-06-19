```agda
module synthetic-homotopy-theory.two-sphere where
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

open import synthetic-homotopy-theory.free-two-loops
open import synthetic-homotopy-theory.free-three-loops
open import synthetic-homotopy-theory.circle
open import structured-types.pointed-equivalences
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### The standard two sphere

```agda
𝕊²-Pointed-Type : Pointed-Type lzero
𝕊²-Pointed-Type = sphere-Pointed-Type 2

𝕊² : UU lzero
𝕊² = type-Pointed-Type 𝕊²-Pointed-Type

base-𝕊² : 𝕊²
base-𝕊² = point-Pointed-Type 𝕊²-Pointed-Type

two-loop-𝕊² : type-Ω² base-𝕊²
two-loop-𝕊² =
  map-pointed-equiv
    (pointed-equiv-2-loop-pointed-identity
      𝕊²-Pointed-Type
      (meridian-sphere 1 (sphere-1-circle base-𝕊¹)))
    (ap (meridian-sphere 1 ∘ sphere-1-circle) loop-𝕊¹)

free-two-loop-𝕊² : free-two-loop 𝕊²
pr1 free-two-loop-𝕊² = base-𝕊²
pr2 free-two-loop-𝕊² = two-loop-𝕊²

3-loop-eckmann-hilton-𝕊² : type-Ω³ base-𝕊²
3-loop-eckmann-hilton-𝕊² = 3-loop-eckmann-hilton-Ω² two-loop-𝕊²

free-3-loop-eckmann-hilton-𝕊² : free-three-loop 𝕊²
pr1 free-3-loop-eckmann-hilton-𝕊² = base-𝕊²
pr2 free-3-loop-eckmann-hilton-𝕊² = 3-loop-eckmann-hilton-𝕊²

module _
  (up : universal-property-two-sphere free-two-loop-𝕊²)
  where

  universal-property-𝕊² : universal-property-two-sphere free-two-loop-𝕊²
  universal-property-𝕊² = up

  equiv-universal-property-𝕊² :
    {l : Level} (X : UU l) → (𝕊² → X) ≃ free-two-loop X
  pr1 (equiv-universal-property-𝕊² X) = ev-free-two-loop free-two-loop-𝕊² X
  pr2 (equiv-universal-property-𝕊² X) = universal-property-𝕊² X

module _
  (up : dependent-universal-property-two-sphere free-two-loop-𝕊²)
  where

  dependent-universal-property-𝕊² : dependent-universal-property-two-sphere free-two-loop-𝕊²
  dependent-universal-property-𝕊² = up

  equiv-dependent-universal-property-𝕊² :
    {l : Level} (P : 𝕊² →  UU l) → ((x : 𝕊²) → P x) ≃ free-dependent-two-loop P free-two-loop-𝕊²
  pr1 (equiv-dependent-universal-property-𝕊² P) = ev-free-two-loop-Π free-two-loop-𝕊² P
  pr2 (equiv-dependent-universal-property-𝕊² P) = dependent-universal-property-𝕊² P

```
