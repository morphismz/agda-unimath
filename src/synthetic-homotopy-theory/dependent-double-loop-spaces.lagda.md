# Dependent double loop spaces

```agda
module synthetic-homotopy-theory.dependent-double-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import foundation.action-on-identifications-dependent-functions
open import foundation.dependent-identifications

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces

open import synthetic-homotopy-theory.double-loop-spaces
open import foundation.transport-along-higher-identifications

open import foundation-core.equivalences
```

</details>

## Idea

A dependent double loop space is an iterated dependent identification, over a two loop, between the trivial dependent identifications.
These have a simplified form, which we compute as equivalent to interated dependent identifications.

## Definition

### Dependent double loop spaces

```agda
module _
  {l1 l2 : Level}
  where

  dependent-Ω² : {A : Pointed-Type l1} (B : type-Pointed-Type A → UU l2) → type-Pointed-Type (Ω² A) → B (point-Pointed-Type A) → UU l2
  dependent-Ω² B s b  = tr² B s b ＝ refl
```
### `dependent-Ω²` are iterated dependent identifications over two loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} (B : X → UU l2) (α : type-Ω² x) (b : B x)
  where

  compute-dependent-identification-Ω² :
    dependent-Ω² B α b ≃ dependent-identification² B α refl refl
  compute-dependent-identification-Ω² = (compute-dependent-identification² B α refl refl) ∘e equiv-concat' refl (inv right-unit) ∘e equiv-inv (tr² B α b) refl
```

### Action of dependent functions on loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} {B : X → UU l2}
  where

  apd²-Ω² : (f : (x : X) → B x) (α : type-Ω² x) → dependent-Ω² B α (f x)
  apd²-Ω² f α = map-inv-equiv (compute-dependent-identification-Ω² B α (f x)) (apd (apd f) α)
```

## Properties

