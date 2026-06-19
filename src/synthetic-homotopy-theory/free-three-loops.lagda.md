# Free two loops

```agda
module synthetic-homotopy-theory.free-three-loops where
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
open import synthetic-homotopy-theory.dependent-triple-loop-spaces
open import synthetic-homotopy-theory.triple-loop-spaces
open import foundation-core.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.transport-along-higher-identifications
open import foundation.action-on-identifications-dependent-functions
open import foundation.homotopies
```

</details>

## Idea

## Definitions

### Free three loops

```agda
free-three-loop : {l1 : Level} (X : UU l1) → UU l1
free-three-loop X = Σ X (λ x → type-Ω³ x)

module _
  {l1 : Level} {X : UU l1}
  where

  base-free-three-loop : free-three-loop X → X
  base-free-three-loop = pr1

  three-loop-free-loop : (α : free-three-loop X) → type-Ω³ (base-free-three-loop α)
  three-loop-free-loop = pr2
```

### Free dependent three loops

```agda
free-dependent-three-loop : {l1 l2 : Level} {X : UU l1} (B : X → UU l2) (α : free-three-loop X) → UU l2
free-dependent-three-loop B α =
  Σ ( B (base-free-three-loop α)) (dependent-Ω³ B (three-loop-free-loop α))

module _
  {l1 l2 : Level} {X : UU l1} (B : X → UU l2) (α : free-three-loop X)
  where

  base-free-dependent-three-loop : free-dependent-three-loop B α → B (base-free-three-loop α)
  base-free-dependent-three-loop = pr1

  three-loop-free-dependent-loop : (s : free-dependent-three-loop B α) → dependent-Ω³ B (three-loop-free-loop α) (base-free-dependent-three-loop s)
  three-loop-free-dependent-loop = pr2
```


## Properties

### Characterization of the identity type of the type of free two loops

### Characterization of the identity type of the type of free dependent two loops
