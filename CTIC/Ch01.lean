import Mathlib
import Mathlib.CategoryTheory.Iso
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Category.Ring.Basic

open CategoryTheory

-- example 1.1.10
open Function in
lemma bijective_iff_iso {X Y : Type} (f : X → Y) : Bijective f ↔ @IsIso Type _ _ _ f := by
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
lemma iso_unique (C : Type) [Category C] (X Y : C) (α α' : Iso X Y) (h : α.hom = α'.hom) : α.inv = α'.inv := by
  obtain ⟨f , g , l , r ⟩ := α
  obtain ⟨f', g', l', r'⟩ := α'
  simp_all
  calc
    g = g ≫  𝟙 X      := Eq.symm (Category.comp_id g)
    _ = g ≫  f' ≫ g'  := congrArg (CategoryStruct.comp g) (id (Eq.symm l'))
    _ = g ≫  f ≫ g'   := by rw [h]
    _ = (g ≫  f) ≫ g' := Eq.symm (Category.assoc g f g')
    _ = (𝟙 Y) ≫ g'    := by rw [r]
    _ = g'            := Category.id_comp g'

-- exercise 1.1.i.ii
lemma inverses_eq (C : Type) [Category C] (X Y : C) (f : X ⟶  Y) (g h : Y ⟶  X) (H : f ≫  g = 𝟙 X) (H' : h ≫ f = 𝟙 Y) : g = h := by
  calc
    g = 𝟙 Y ≫ g     := Eq.symm (Category.id_comp g)
    _ = (h ≫ f) ≫ g := by rw [H']
    _ = h ≫ f ≫ g   := Category.assoc h f g
    _ = h ≫ 𝟙 X     := by rw [H]
    _ = h           := Category.comp_id h

lemma inverses_iso (C : Type) [Category C] (X Y : C) (f : X ⟶  Y) (g h : Y ⟶  X) (H : f ≫  g = 𝟙 X) (H' : h ≫ f = 𝟙 Y) : IsIso f := by
  exists h
  rw [inverses_eq C X Y f g h H H'] at H
  exact ⟨H, H'⟩

section isocomp

variable {α : Type} [C : Category α] {x y : α} (f : x ⟶  y)

-- lemma 1.2.3
-- chance to try duality....
lemma iso_postcomp : IsIso f ↔ (∀ c, @IsIso Type _ _ _ (λ h : c ⟶  x ↦ h ≫ f)) := by
  apply Iff.intro <;> intros h
  case mp =>
    have ⟨g, ⟨l, r⟩⟩ := h
    intros c
    exists (· ≫ g)
    apply And.intro <;> ext <;> simp [l, r, Category.comp_id]
  case mpr => 
    sorry

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

-- lemma 1.3.8
lemma iso_functor {C D : Type} [Category C] [Category D] (F : C ⥤ D) {x y : C} (f : x ⟶  y) : IsIso f → IsIso (F.map f) := by
  intros h
  have ⟨g, ⟨l, r⟩⟩ := h
  exists F.map g
  apply And.intro <;> rw [←CategoryTheory.Functor.map_id]
  case left =>
    rw [←l,CategoryTheory.Functor.map_comp]
  case right =>
    rw [←r, CategoryTheory.Functor.map_comp]
