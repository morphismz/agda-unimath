# Universal property of the two sphere
```agda
module synthetic-homotopy-theory.universal-property-two-sphere where
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
```

</details>

## Definitions

### Evaluating an ordinary function at a free two loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-two-loop X) (Y : UU l2)
  where

  ev-free-two-loop : (X → Y) → free-two-loop Y
  pr1 (ev-free-two-loop f) = f (base-free-two-loop α)
  pr2 (ev-free-two-loop f) = ap² f (two-loop-free-loop α)
```


### Universal property of the two sphere

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-two-loop X)
  where

  universal-property-two-sphere : UUω
  universal-property-two-sphere =
    {l : Level} (Y : UU l) → is-equiv (ev-free-two-loop α Y)
```

### Evaluating an dependent function at a free two loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-two-loop X) (B : X → UU l2)
  where

  ev-free-two-loop-Π : ((x : X) → B x) → free-dependent-two-loop B α
  pr1 (ev-free-two-loop-Π f) = f (base-free-two-loop α)
  pr2 (ev-free-two-loop-Π f) = apd²-Ω² f (two-loop-free-loop α)
```

### Dependent universal property of the two sphere

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-two-loop X)
  where

  dependent-universal-property-two-sphere : UUω
  dependent-universal-property-two-sphere =
    {l2 : Level} (B : X → UU l2) → is-equiv (ev-free-two-loop-Π α B)
```
