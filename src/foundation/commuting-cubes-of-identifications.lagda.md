# Path algebra

```agda
module foundation.commuting-cubes-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.commuting-squares-of-identifications
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-identifications-concatenation
```

## Idea

To Do

Cube goes back left bottom to front right top. This generalizes the
square square identifications going left bottom to top right. This
way, one can think of the cube as going from left to right, better
aliging with the standard direction of paths.

## Definitions

```agda
module _
  {l : Level} {A : UU l} {x000 x001 x010 x100 x011 x101 x110 x111 : A}
  where

  coherence-cube-identifications :
    (p000̂ : x000 ＝ x001) (p00̂0 : x000 ＝ x010) (p0̂00 : x000 ＝ x100)
    (p00̂1 : x001 ＝ x011) (p0̂01 : x001 ＝ x101) (p010̂ : x010 ＝ x011)
    (p0̂10 : x010 ＝ x110) (p100̂ : x100 ＝ x101) (p10̂0 : x100 ＝ x110)
    (p0̂11 : x011 ＝ x111) (p10̂1 : x101 ＝ x111) (p110̂ : x110 ＝ x111)
    (front : coherence-square-identifications p00̂0 p000̂ p010̂ p00̂1)
    (left : coherence-square-identifications p0̂00 p000̂ p100̂ p0̂01)
    (top : coherence-square-identifications p0̂00 p00̂0 p10̂0 p0̂10)
    (bottom : coherence-square-identifications p0̂01 p00̂1 p10̂1 p0̂11)
    (right : coherence-square-identifications p0̂10 p010̂ p110̂ p0̂11)
    (back : coherence-square-identifications p10̂0 p100̂ p110̂ p10̂1) → UU l
  coherence-cube-identifications
    p000̂ p00̂0 p0̂00 p00̂1 p0̂01 p010̂ p0̂10 p100̂ p10̂0 p0̂11 p10̂1 p110̂
    front left top bottom right back =
    Id
      ( ( assoc p000̂ p00̂1 p0̂11) ∙
        ( ( left-whisker-concat p000̂ bottom) ∙
          ( ( inv (assoc p000̂ p0̂01 p10̂1)) ∙
            ( ( right-whisker-concat left p10̂1) ∙
              ( ( assoc p0̂00 p100̂ p10̂1) ∙
                ( ( left-whisker-concat p0̂00 back )))))))
      ( ( right-whisker-concat front p0̂11) ∙
        ( ( assoc p00̂0 p010̂ p0̂11) ∙
          ( ( left-whisker-concat p00̂0 right) ∙
            ( ( inv (assoc p00̂0 p0̂10 p110̂)) ∙
              ( ( right-whisker-concat top p110̂) ∙
                ( assoc p0̂00 p10̂0 p110̂))))))
```

