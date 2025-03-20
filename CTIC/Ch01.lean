import Mathlib
import Mathlib.CategoryTheory.Iso
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Category.Ring.Basic

open CategoryTheory

-- example 1.1.10
open Function in
example (X Y : Type) (f : X → Y) : Bijective f ↔ @IsIso Type _ _ _ f := by
  apply Iff.intro <;> intros h 
  case mp =>
    -- there's weirdness about the defeq of the bundling, but this is the idea...
    exists (Equiv.ofBijective f h).invFun
    apply And.intro
    case left =>
      have left_inv := (Equiv.ofBijective f h).left_inv
      exact types_ext (f ≫ (Equiv.ofBijective f h).invFun) (𝟙 X) left_inv
    case right =>
      have right_inv := (Equiv.ofBijective f h).right_inv
      exact types_ext ((Equiv.ofBijective f h).invFun ≫ f) (𝟙 Y) right_inv
  case mpr =>
    obtain ⟨finv, ⟨l, r⟩⟩ := h.out
    constructor
    case left =>
      apply HasLeftInverse.injective
      exists finv
      exact congrFun l
    case right =>
      apply HasRightInverse.surjective
      exists finv
      exact congrFun r

-- exercise 1.1.i.i
-- TODO: write this in calc style
example (C : Type) [Category C] (X Y : C) (α α' : Iso X Y) (h : α.hom = α'.hom) : α.inv = α'.inv := by
  obtain ⟨f , g , l , r ⟩ := α
  obtain ⟨f', g', l', r'⟩ := α'
  simp_all
  sorry

-- exercise 1.1.i.ii
example (C : Type) [Category C] (X Y : C) (f : X ⟶  Y) (g h : Y ⟶  X) (H : f ≫  g = 𝟙 X) (H' : h ≫ f = 𝟙 Y) : g = h := by
  sorry      

section isocomp

variable {α : Type} [C : Category α] {x y : α} (f : x ⟶  y)

-- lemma 1.2.3
-- chance to try duality....
lemma iso_postcomp : IsIso f ↔ (∀ c, @IsIso Type _ _ _ (λ g : c ⟶  x ↦ g ≫ f)) := sorry
lemma iso_precomp  : IsIso f ↔ (∀ c, @IsIso Type _ _ _ (λ g : y ⟶  c ↦ f ≫ g)) := sorry

-- exercise 1.2.ii
-- book states this as surjective, but I think easier (since in Set/Type) to use equivalent Epi
lemma split_epi_postcomp  : IsSplitEpi  f ↔  (∀ c, @Epi Type _ _ _ (λ g : c ⟶  x ↦ g ≫ f)) := sorry
lemma split_mono_postcomp : IsSplitMono f ↔  (∀ c, @Epi Type _ _ _ (λ g : y ⟶  c ↦ f ≫ g)) := sorry

end isocomp

-- exercise 1.2.v
-- pain in the ass bundling, meta here???
example : Mono (RingCat.ofHom (Int.castRingHom ℚ)) := by
  sorry

example : Epi (RingCat.ofHom (Int.castRingHom ℚ)) := by
  sorry
