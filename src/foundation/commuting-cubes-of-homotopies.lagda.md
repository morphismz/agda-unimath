# Path algebra

```agda
module foundation.commuting-cubes-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.commuting-cubes-of-identifications
open import foundation.commuting-squares-of-homotopies
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-concatenation

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-identifications-concatenation
```

## Idea

To Do

Cube goes back left bottom to front right top. This generalizes the
square square homotopies going left bottom to top right. This
way, one can think of the cube as going from left to right, better
aliging with the standard direction of paths.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f000 f001 f010 f100 f011 f101 f110 f111 : (x : A) → B x}
  where

  coherence-cube-homotopies :
    (H000̂ : f000 ~ f001) (H00̂0 : f000 ~ f010) (H0̂00 : f000 ~ f100)
    (H00̂1 : f001 ~ f011) (H0̂01 : f001 ~ f101) (H010̂ : f010 ~ f011)
    (H0̂10 : f010 ~ f110) (H100̂ : f100 ~ f101) (H10̂0 : f100 ~ f110)
    (H0̂11 : f011 ~ f111) (H10̂1 : f101 ~ f111) (H110̂ : f110 ~ f111)
    (front : coherence-square-homotopies H00̂0 H000̂ H010̂ H00̂1)
    (left : coherence-square-homotopies H0̂00 H000̂ H100̂ H0̂01)
    (top : coherence-square-homotopies H0̂00 H00̂0 H10̂0 H0̂10)
    (bottom : coherence-square-homotopies H0̂01 H00̂1 H10̂1 H0̂11)
    (right : coherence-square-homotopies H0̂10 H010̂ H110̂ H0̂11)
    (back : coherence-square-homotopies H10̂0 H100̂ H110̂ H10̂1) → UU (l1 ⊔ l2)
  coherence-cube-homotopies
    H000̂  H00̂0 H0̂00 H00̂1 H0̂01 H010̂  H0̂10 H100̂  H10̂0 H0̂11 H10̂1 H110̂
    front left top bottom right back =
    ( ( assoc-htpy H000̂ H00̂1 H0̂11) ∙h
      ( left-whisker-concat-htpy H000̂  bottom) ∙h
        (inv-htpy (assoc-htpy H000̂ H0̂01 H10̂1)) ∙h
          ( right-whisker-concat-htpy left H10̂1) ∙h
            ( assoc-htpy H0̂00 H100̂ H10̂1) ∙h
              ( left-whisker-concat-htpy H0̂00  back)) ~
    ( ( right-whisker-concat-htpy front H0̂11) ∙h
      ( assoc-htpy H00̂0 H010̂  H0̂11) ∙h
        ( left-whisker-concat-htpy H00̂0 right) ∙h
          ( inv-htpy (assoc-htpy H00̂0 H0̂10 H110̂)) ∙h
            ( right-whisker-concat-htpy top H110̂) ∙h
              (assoc-htpy H0̂00 H10̂0 H110̂ ))
```

### Properties

Composition of cubes

filing partial cubes
