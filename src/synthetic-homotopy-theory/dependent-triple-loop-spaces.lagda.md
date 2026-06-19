# Dependent double triple spaces

```agda
module synthetic-homotopy-theory.dependent-triple-loop-spaces where
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

open import synthetic-homotopy-theory.triple-loop-spaces
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

  dependent-Ω³ : {A : Pointed-Type l1} (B : type-Pointed-Type A → UU l2) → type-Pointed-Type (Ω³ A) → B (point-Pointed-Type A) → UU l2
  dependent-Ω³ B s b  = tr³ B s b ＝ refl
```
### `dependent-Ω³` are iterated dependent identifications over two loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} (B : X → UU l2) (α : type-Ω³ x) (b : B x)
  where

  compute-dependent-identification-Ω³ :
    dependent-Ω³ B α b ≃ dependent-identification³ B α (refl-Ω² {a = b}) (refl-Ω² {a = b})
  compute-dependent-identification-Ω³ =
    compute-dependent-identification³ B α (refl-Ω² {a = b}) (refl-Ω² {a = b}) ∘e
    inv-equiv (equiv-concat (right-unit ∙ right-unit-law-right-whisker-concat (tr³ B α b) ∙ right-unit) refl) ∘e
    equiv-inv refl (tr³ B α b ∙ refl) ∘e
    equiv-concat' refl (inv right-unit) ∘e
    equiv-inv (tr³ B α b) refl
```

### Action of dependent functions on loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} {B : X → UU l2}
  where

  apd³-Ω³ : (f : (x : X) → B x) (α : type-Ω³ x) → dependent-Ω³ B α (f x)
  apd³-Ω³ f α = map-inv-equiv (compute-dependent-identification-Ω³ B α (f x)) (apd (apd (apd f)) α)
```

## Properties

```agda

```
