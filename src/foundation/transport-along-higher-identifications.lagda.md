# Transport along higher identifications

```agda
module foundation.transport-along-higher-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
open import foundation.whiskering-identifications-concatenation

open import foundation-core.transport-along-identifications
```

</details>

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  where

  tr² : (B : A → UU l2) (α : p ＝ p') (b : B x) → (tr B p b) ＝ (tr B p' b)
  tr² B α b = ap (λ t → tr B t b) α

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b : B x) → (tr² B α b) ＝ (tr² B α' b)
  tr³ B β b = ap (λ t → tr² B t b) β
```

### Computing 2-dimensional transport in a family of identifications with a fixed source

```agda
module _
  {l : Level} {A : UU l} {a b c : A} {q q' : b ＝ c}
  where

  tr²-Id-right :
    (α : q ＝ q') (p : a ＝ b) →
    coherence-square-identifications
      ( tr-Id-right q p)
      ( tr² (Id a) α p)
      ( left-whisker-concat p α)
      ( tr-Id-right q' p)
  tr²-Id-right α p =
    inv-nat-htpy (λ (t : b ＝ c) → tr-Id-right t p) α
```

### Coherences and algebraic identities for `tr²`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : x ＝ y} (α : p ＝ p') (α' : p' ＝ p'') (b : B x) →
    (tr² B (α ∙ α') b) ＝ (tr² B α b ∙ tr² B α' b)
  tr²-concat α α' b = ap-concat (λ t → tr B t b) α α'

module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-left-whisker :
    (p : x ＝ y) {q q' : y ＝ z} (β : q ＝ q') (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (left-whisker-concat p β) b)
      ( right-whisker-comp (tr² B β) (tr B p) b)
      ( tr-concat p q' b)
  tr²-left-whisker refl refl b = refl

  tr²-right-whisker :
    {p p' : x ＝ y} (α : p ＝ p') (q : y ＝ z) (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (right-whisker-concat α q) b)
      ( left-whisker-comp (tr B q) (tr² B α) b)
      ( tr-concat p' q b)
  tr²-right-whisker refl refl b = inv right-unit
```

### Coherences and algebraic identities for `tr³`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {B : A → UU l2}
  where

  tr³-concat :
    {α α' α'' : p ＝ p'} (γ : α ＝ α') (δ : α' ＝ α'') →
    tr³ B (γ ∙ δ) ~ (tr³ B γ) ∙h (tr³ B δ)
  tr³-concat γ δ b = ap-concat (λ t → tr² B t b) γ δ

```

#### A coherence computing transport along commutative-left-whisker-right-whisker-concat

This coherence naturally takes the form of a filler for a cube whose
left face is `tr³ (commutative-left-whisker-right-whisker-concat β α)`
and whose right face is
`commutative-right-whisker-left-whisker-htpy (tr² B β) (tr² B α)`

##### The top and bottom faces of the cube, respectively

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2} {p p' : x ＝ y} {q q' : y ＝ z}
  where

  tr²-concat-right-whisker-left-whisker-concat :
    (α : p ＝ p') (β : q ＝ q') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B ((right-whisker-concat α q) ∙ (left-whisker-concat p' β)))
      ( ( ( tr B q) ·l (tr² B α)) ∙h ((tr² B β) ·r (tr B p')))
      ( tr-concat p' q')      
  tr²-concat-right-whisker-left-whisker-concat α β =
    ( right-whisker-concat-htpy
      ( tr²-concat
        ( right-whisker-concat α q)
        ( left-whisker-concat p' β))
      ( tr-concat p' q')) ∙h
    ( vertical-pasting-coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (right-whisker-concat α q))
      ( left-whisker-comp (tr B q) (tr² B α))
      ( tr-concat p' q)
      ( tr² B (left-whisker-concat p' β))
      ( right-whisker-comp (tr² B β) (tr B p'))
      ( tr-concat p' q')
      ( tr²-right-whisker α q)
      ( tr²-left-whisker p' β))

  tr²-concat-left-whisker-right-whisker-concat :
    (β : q ＝ q') (α : p ＝ p') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B ((left-whisker-concat p β) ∙ (right-whisker-concat α q')))
      ( ((tr² B β) ·r (tr B p)) ∙h ((tr B q') ·l (tr² B α)))
      ( tr-concat p' q')
  tr²-concat-left-whisker-right-whisker-concat β α =
    ( right-whisker-concat-htpy
      ( tr²-concat
        ( left-whisker-concat p β)
        ( right-whisker-concat α q'))
      ( tr-concat p' q')) ∙h
    ( vertical-pasting-coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (left-whisker-concat p β))
      ( right-whisker-comp (tr² B β) (tr B p))
      ( tr-concat p q')
      ( tr² B (right-whisker-concat α q'))
      ( left-whisker-comp (tr B q') (tr² B α))
      ( tr-concat p' q')
      ( tr²-left-whisker p β)
      ( tr²-right-whisker α q'))
```

##### The cube

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-commutative-htpy-commutative-concat-coherence-cube-homotopies :
    {!coherence-cube-homotopies
      !}
  tr³-commutative-htpy-commutative-concat-coherence-cube-homotopies = {!!}

```

Since the front and back faces of this cube are trivial, there is a
simplified form of this coherence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-commutative-htpy-commutative-concat :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-homotopies
      ( tr²-concat-left-whisker-right-whisker-concat β α)
      ( right-whisker-concat-htpy
        ( tr³
          ( B)
          ( commutative-left-whisker-right-whisker-concat β α))
        ( tr-concat p' q'))
      ( left-whisker-concat-htpy
        ( tr-concat p q)
        ( commutative-right-whisker-left-whisker-htpy (tr² B β) (tr² B α)))
      ( tr²-concat-right-whisker-left-whisker-concat α β)
  tr³-commutative-htpy-commutative-concat {q = refl} refl {p = refl} refl =
    refl-htpy

```








The above coherences simplify when α and β are 2-loops.

TODO -- How do this? Make cube lemmas?? E.g. if front and back face are trivial, then...


OR square lemmas? e.g., pasting unit laws?

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A}
  {B : A → UU l2}
  where

  tr²-concat-left-whisker-right-whisker-concat-Ω² :
    (β : refl {x = a} ＝ refl) (α : refl {x = a} ＝ refl) →
    (tr² B ((left-whisker-concat refl β) ∙ (right-whisker-concat α refl))) ~
    (((tr² B β) ·r (tr B refl)) ∙h ((tr B refl) ·l (tr² B α)))
  tr²-concat-left-whisker-right-whisker-concat-Ω² β α x =
    concat
      {x = ( tr² B ((left-whisker-concat refl β) ∙ (right-whisker-concat α refl)) x)}
      ( inv right-unit)
      ( ( ((tr² B β) ·r (tr B refl)) ∙h ((tr B refl) ·l (tr² B α))) x)
      ( tr²-concat-left-whisker-right-whisker-concat β α x)
  
  tr²-concat-right-whisker-left-whisker-concat-Ω² :
    (α : refl {x = a} ＝ refl) (β : refl {x = a} ＝ refl) →
    (tr² B ((right-whisker-concat α refl) ∙ (left-whisker-concat refl β))) ~
    (((tr B refl) ·l (tr² B α)) ∙h ((tr² B β) ·r (tr B refl)))
  tr²-concat-right-whisker-left-whisker-concat-Ω² α β = {!!}
  
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-commutative-htpy-commutative-concat-Ω² :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-homotopies
      ( tr²-concat-left-whisker-right-whisker-concat β α)
      ( right-whisker-concat-htpy
        ( tr³
          ( B)
          ( commutative-left-whisker-right-whisker-concat β α))
        ( tr-concat p' q'))
      ( left-whisker-concat-htpy
        ( tr-concat p q)
        ( commutative-right-whisker-left-whisker-htpy (tr² B β) (tr² B α)))
      ( tr²-concat-right-whisker-left-whisker-concat α β)
  tr³-commutative-htpy-commutative-concat-Ω² {q = refl} refl {p = refl} refl =
    refl-htpy
```
