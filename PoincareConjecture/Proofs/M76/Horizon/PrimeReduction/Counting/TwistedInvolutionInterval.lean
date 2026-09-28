import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FreeInvolutionQuotient
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.TwistedProjectiveInterval

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set CategoryTheory Limits
open scoped Topology

universe u

namespace PoincareConjecture.M76.TwistedInvolutionInterval

variable {S : Type u} [TopologicalSpace S] (τ : S ≃ₜ S)
  (hτ : Function.Involutive τ)

def deck : (S × unitInterval) ≃ₜ (S × unitInterval) :=
  τ.prodCongr unitInterval.symmHomeomorph

include hτ in
theorem deck_involutive : Function.Involutive (deck τ) := fun z =>
  Prod.ext (hτ z.1) (unitInterval.symm_symm z.2)

theorem deck_ne (hfree : ∀ x, τ x ≠ x) (z : S × unitInterval) : deck τ z ≠ z :=
  fun h => hfree z.1 (congrArg Prod.fst h)

abbrev Model := FreeInvolutionQuotient.Model (deck τ) (deck_involutive τ hτ)

def projection : S × unitInterval → Model τ hτ :=
  FreeInvolutionQuotient.projection (deck τ) (deck_involutive τ hτ)

theorem projection_eq (x y : S × unitInterval) :
    projection τ hτ x = projection τ hτ y ↔ x = y ∨ x = deck τ y :=
  FreeInvolutionQuotient.projection_eq _ _ x y

theorem projection_deck (x : S × unitInterval) :
    projection τ hτ (deck τ x) = projection τ hτ x :=
  FreeInvolutionQuotient.projection_involution _ _ x

theorem continuous_projection : Continuous (projection τ hτ) :=
  FreeInvolutionQuotient.continuous_projection _ _

theorem projection_isCoveringMap [T2Space S] (hfree : ∀ x, τ x ≠ x) :
    IsCoveringMap (projection τ hτ) :=
  FreeInvolutionQuotient.projection_isCoveringMap _ _ (deck_ne τ hfree)

abbrev midpoint := TwistedProjectiveInterval.midpoint

def zeroSection : Set (Model τ hτ) := projection τ hτ '' {z | z.2 = midpoint}

def boundary : Set (Model τ hτ) := projection τ hτ '' {z | z.2 = 0 ∨ z.2 = 1}

def boundaryMap (x : S) : Model τ hτ := projection τ hτ (x, 0)

theorem boundaryMap_injective : Function.Injective (boundaryMap τ hτ) := by
  intro x y h
  rcases (projection_eq τ hτ (x, 0) (y, 0)).mp h with h | h
  · exact congrArg Prod.fst h
  · have ht := congrArg (fun z : S × unitInterval => (z.2 : ℝ)) h
    norm_num [deck, unitInterval.symmHomeomorph, unitInterval.symm] at ht

theorem range_boundaryMap : range (boundaryMap τ hτ) = boundary τ hτ := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(x, 0), Or.inl rfl, rfl⟩
  · rintro _ ⟨⟨x, t⟩, ht, rfl⟩
    rcases ht with ht | ht
    · exact ⟨x, congrArg (projection τ hτ) (Prod.ext rfl ht.symm)⟩
    · refine ⟨τ x, ?_⟩
      apply (projection_eq τ hτ _ _).mpr
      right
      apply Prod.ext
      · rfl
      · change 0 = unitInterval.symm t
        rw [show t = 1 from ht]
        simp

def boundaryHomeomorph [CompactSpace S] [T2Space S] : S ≃ₜ boundary τ hτ :=
  (((continuous_projection τ hτ).comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
    (boundaryMap_injective τ hτ)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_boundaryMap τ hτ))

theorem boundaryHomeomorph_apply [CompactSpace S] [T2Space S] (x : S) :
    (boundaryHomeomorph τ hτ x : Model τ hτ) = projection τ hτ (x, 0) := rfl

theorem projection_top (x : S) :
    projection τ hτ (x, 1) = boundaryMap τ hτ (τ x) := by
  apply (projection_eq τ hτ _ _).mpr
  right
  apply Prod.ext (hτ x).symm
  change 1 = unitInterval.symm 0
  simp

theorem range_projection_top : range (fun x => projection τ hτ (x, 1)) = boundary τ hτ := by
  rw [show (fun x => projection τ hτ (x, 1)) = boundaryMap τ hτ ∘ τ from
    funext (projection_top τ hτ)]
  rw [range_comp, τ.surjective.range_eq, image_univ, range_boundaryMap]

def zeroSectionMap : FreeInvolutionQuotient.Model τ hτ → Model τ hτ :=
  Quotient.lift (fun x : S => projection τ hτ (x, midpoint)) (by
    intro x y h
    rcases h with h | h
    · exact congrArg (fun x => projection τ hτ (x, midpoint)) h
    · apply (projection_eq τ hτ _ _).mpr
      right
      exact Prod.ext h TwistedProjectiveInterval.symm_midpoint.symm)

theorem continuous_zeroSectionMap : Continuous (zeroSectionMap τ hτ) :=
  ((continuous_projection τ hτ).comp (continuous_id.prodMk continuous_const)).quotient_lift _

theorem zeroSectionMap_injective : Function.Injective (zeroSectionMap τ hτ) := by
  intro x y h
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      rcases (projection_eq τ hτ (x, midpoint) (y, midpoint)).mp h with h | h
      · exact Quotient.sound (Or.inl (congrArg Prod.fst h))
      · exact Quotient.sound (Or.inr (congrArg Prod.fst h))

theorem range_zeroSectionMap : range (zeroSectionMap τ hτ) = zeroSection τ hτ := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Quotient.inductionOn with | _ x =>
      exact ⟨(x, midpoint), rfl, rfl⟩
  · rintro _ ⟨⟨x, t⟩, ht, rfl⟩
    exact ⟨FreeInvolutionQuotient.projection τ hτ x,
      congrArg (projection τ hτ) (Prod.ext rfl ht.symm)⟩

def zeroSectionHomeomorph [CompactSpace S] [T2Space S] :
    FreeInvolutionQuotient.Model τ hτ ≃ₜ zeroSection τ hτ :=
  ((continuous_zeroSectionMap τ hτ).isClosedEmbedding
    (zeroSectionMap_injective τ hτ)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_zeroSectionMap τ hτ))

theorem zeroSectionHomeomorph_apply [CompactSpace S] [T2Space S] (x : S) :
    (zeroSectionHomeomorph τ hτ (FreeInvolutionQuotient.projection τ hτ x) : Model τ hτ) =
      projection τ hτ (x, midpoint) := rfl

theorem projection_mem_zeroSection (z : S × unitInterval) :
    projection τ hτ z ∈ zeroSection τ hτ ↔ z.2 = midpoint := by
  constructor
  · rintro ⟨w, hw, h⟩
    rcases (projection_eq τ hτ w z).mp h with h | h
    · exact (congrArg Prod.snd h).symm.trans hw
    · have he : unitInterval.symm z.2 = midpoint := (congrArg Prod.snd h).symm.trans hw
      have hi := congrArg unitInterval.symm he
      simpa only [unitInterval.symm_symm, TwistedProjectiveInterval.symm_midpoint] using hi
  · intro h
    exact ⟨z, h, rfl⟩

theorem projection_mem_boundary (z : S × unitInterval) :
    projection τ hτ z ∈ boundary τ hτ ↔ z.2 = 0 ∨ z.2 = 1 := by
  constructor
  · rintro ⟨w, hw, h⟩
    rcases (projection_eq τ hτ w z).mp h with h | h
    · exact h ▸ hw
    · have he : w.2 = unitInterval.symm z.2 := congrArg Prod.snd h
      rcases hw with hw | hw
      · right
        have hi := congrArg unitInterval.symm (he.symm.trans hw)
        simpa using hi
      · left
        have hi := congrArg unitInterval.symm (he.symm.trans hw)
        simpa using hi
  · intro h
    exact ⟨z, h, rfl⟩

theorem zeroSection_disjoint_boundary : Disjoint (zeroSection τ hτ) (boundary τ hτ) := by
  apply disjoint_left.mpr
  intro x hx hb
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
  have hz := (projection_mem_zeroSection τ hτ z).mp hx
  rcases (projection_mem_boundary τ hτ z).mp hb with he | he
  · have hh := congrArg Subtype.val (hz.symm.trans he)
    norm_num [midpoint, TwistedProjectiveInterval.midpoint] at hh
  · have hh := congrArg Subtype.val (hz.symm.trans he)
    norm_num [midpoint, TwistedProjectiveInterval.midpoint] at hh

theorem exists_homology_retract [T2Space S] [PathConnectedSpace S]
    (hfree : ∀ x, τ x ≠ x) (R : ModuleCat.{u} (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of (Model τ hτ))).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of (Model τ hτ))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  let x : S := Classical.arbitrary _
  let f : C(S, S × unitInterval) :=
    ⟨fun y => (y, midpoint), continuous_id.prodMk continuous_const⟩
  let P := (PathConnectedSpace.somePath x (τ x)).map f.continuous
  have he : deck τ (x, midpoint) = f (τ x) :=
    Prod.ext rfl TwistedProjectiveInterval.symm_midpoint
  exact AntipodalCover.exists_homology_retract (projection τ hτ) (deck τ)
    (deck_involutive τ hτ) (deck_ne τ hfree) (projection_eq τ hτ)
    (projection_isCoveringMap τ hτ hfree) Quotient.mk_surjective R (x, midpoint)
    (P.cast rfl he)

theorem h1_not_isZero [T2Space S] [PathConnectedSpace S]
    (hfree : ∀ x, τ x ≠ x) (R : ModuleCat.{u} (ZMod 2)) [Nontrivial R] :
    ¬ IsZero ((TopCat.toSSet.obj (TopCat.of (Model τ hτ))).homology R 1) := by
  obtain ⟨i, r, hir⟩ := exists_homology_retract τ hτ hfree R
  intro hzero
  have hi : i = 0 := hzero.eq_of_tgt i 0
  have hid : 𝟙 R = 0 := hir.symm.trans (by rw [hi, zero_comp])
  have : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero R).mpr hid)
  exact false_of_nontrivial_of_subsingleton R

theorem sphere_h1_not_isZero [T2Space S] (H : S ≃ₜ UnitTwoSphere)
    (hfree : ∀ x, τ x ≠ x) (R : ModuleCat.{u} (ZMod 2)) [Nontrivial R] :
    ¬ IsZero ((TopCat.toSSet.obj (TopCat.of (Model τ hτ))).homology R 1) := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : PathConnectedSpace S := H.symm.surjective.pathConnectedSpace H.symm.continuous
  exact h1_not_isZero τ hτ hfree R

end PoincareConjecture.M76.TwistedInvolutionInterval
