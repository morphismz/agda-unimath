# Universal property of the three sphere

```agda
module synthetic-homotopy-theory.universal-property-three-sphere where
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

open import synthetic-homotopy-theory.free-three-loops
open import synthetic-homotopy-theory.dependent-triple-loop-spaces

open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.triple-loop-spaces
```

</details>

## Definitions

### Evaluating an ordinary function at a free three loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-three-loop X) (Y : UU l2)
  where

  ev-free-three-loop : (X → Y) → free-three-loop Y
  pr1 (ev-free-three-loop f) = f (base-free-three-loop α)
  pr2 (ev-free-three-loop f) = ap (ap² f) (three-loop-free-loop α)
```


### Universal property of the three sphere

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-three-loop X)
  where

  universal-property-three-sphere : UUω
  universal-property-three-sphere =
    {l : Level} (Y : UU l) → is-equiv (ev-free-three-loop α Y)
```

### Evaluating an dependent function at a free three loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-three-loop X) (B : X → UU l2)
  where

  ev-free-three-loop-Π : ((x : X) → B x) → free-dependent-three-loop B α
  pr1 (ev-free-three-loop-Π f) = f (base-free-three-loop α)
  pr2 (ev-free-three-loop-Π f) = apd³-Ω³ f (three-loop-free-loop α)
```

### Dependent universal property of the three sphere

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-three-loop X)
  where

  dependent-universal-property-three-sphere : UUω
  dependent-universal-property-three-sphere =
    {l2 : Level} (B : X → UU l2) → is-equiv (ev-free-three-loop-Π α B)
```
