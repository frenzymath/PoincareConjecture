import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.CylinderLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Winding
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.HomotopicRimExtension
import PoincareConjecture.Proofs.M76.Mathlib.CoveringProduct

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "C64" => AddCircle (4 * (16 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => unitInterval

theorem exists_relative_annulus_covering_of_rim_extension
    (f : C(Ann, I × C64)) (g : C(C32, C64)) (hg : IsCoveringMap g)
    (U : C32 ≃ₜ C32) (L : (ContinuousMap.id C32).Homotopy (U : C(C32, C32)))
    (hlift : ∀ t z, g (L (t, z)) = (f (annulusCylinderHomeomorph (t, z))).2)
    (hnormal : ∀ side z, (f (annulusRimPoint side z)).1 = if side then 1 else 0)
    (A : Ann ≃ₜ Ann) (hA : A.IsFinitePL)
    (hA0 : ∀ z, A (annulusRimPoint false z) = annulusRimPoint false z)
    (hA1 : ∀ z, A (annulusRimPoint true z) = annulusRimPoint true (U z)) :
    ∃ D : Ann ≃ₜ Ann, D.IsFinitePL ∧
      ∃ c : C(Ann, I × C64), IsCoveringMap c ∧
        (∀ x, c x =
          ((annulusCylinderHomeomorph.symm (D x)).1,
            g (annulusCylinderHomeomorph.symm (D x)).2)) ∧
        Nonempty (f.HomotopyRel c annulusRims) := by
  let C := annulusCylinderHomeomorph
  let lift : C(Ann, I × C32) :=
    ⟨fun x => ((f x).1, L (C.symm x)), by fun_prop⟩
  have hlift0 (z : C32) : lift (annulusRimPoint false z) = (0, z) := by
    apply Prod.ext
    · exact hnormal false z
    · change L (C.symm (annulusRimPoint false z)) = z
      rw [← annulusCylinderHomeomorph_zero, Homeomorph.symm_apply_apply, L.apply_zero]
      rfl
  have hlift1 (z : C32) : lift (annulusRimPoint true z) = (1, U z) := by
    apply Prod.ext
    · exact hnormal true z
    · change L (C.symm (annulusRimPoint true z)) = U z
      rw [← annulusCylinderHomeomorph_one, Homeomorph.symm_apply_apply, L.apply_one]
      rfl
  let normalized := lift.comp ⟨A.symm, A.symm.continuous⟩
  have hrims (side : Bool) (z : C32) :
      normalized (annulusRimPoint side z) = (if side then 1 else 0, z) := by
    cases side
    · change lift (A.symm (annulusRimPoint false z)) = _
      rw [← hA0 z, A.symm_apply_apply, hlift0]
      rfl
    · change lift (A.symm (annulusRimPoint true z)) = _
      rw [← U.apply_symm_apply z, ← hA1, A.symm_apply_apply, hlift1, U.apply_symm_apply]
      rfl
  obtain ⟨T, hT, hTrims, ⟨HT⟩⟩ := exists_annulus_winding_correction normalized hrims
  let D := A.trans T.symm
  let c : C(Ann, I × C64) :=
    ⟨fun x => ((C.symm (D x)).1, g (C.symm (D x)).2), by fun_prop⟩
  have hc : IsCoveringMap c :=
    hg.id_prod.comp_homeomorph (D.trans C.symm)
  have hstart (x : Ann) :
      ((HT (0, D x)).1, g (HT (0, D x)).2) = f x := by
    rw [HT.apply_zero]
    change ((lift (A.symm (T (T.symm (A x))))).1,
      g (lift (A.symm (T (T.symm (A x))))).2) = f x
    rw [T.apply_symm_apply, A.symm_apply_apply]
    apply Prod.ext
    · rfl
    · change g (L (C.symm x)) = (f x).2
      have h := hlift (C.symm x).1 (C.symm x).2
      change g (L (C.symm x)) = (f (C (C.symm x))).2 at h
      simpa only [C.apply_symm_apply] using h
  have hDmark (x : Ann) (hx : x ∈ annulusRims) : D x ∈ annulusRims := by
    rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · change T.symm (A (annulusRimPoint false z)) ∈ annulusRims
      rw [hA0, ← hTrims false z, T.symm_apply_apply]
      exact Or.inl ⟨z, rfl⟩
    · change T.symm (A (annulusRimPoint true z)) ∈ annulusRims
      rw [hA1, ← hTrims true (U z), T.symm_apply_apply]
      exact Or.inr ⟨U z, rfl⟩
  refine ⟨D, hA.trans hT.symm, c, hc, fun _ => rfl, ⟨{
    toFun := fun z => ((HT (z.1, D z.2)).1, g (HT (z.1, D z.2)).2)
    continuous_toFun := by fun_prop
    map_zero_left := hstart
    map_one_left := by intro x; rw [HT.apply_one]; rfl
    prop' := by
      intro t x hx
      change ((HT (t, D x)).1, g (HT (t, D x)).2) = f x
      rw [HT.eq_fst t (hDmark x hx)]
      have h := hstart x
      rw [HT.apply_zero] at h
      exact h }⟩⟩

noncomputable def annulusTargetReflection (reverse : Bool) : (I × C64) ≃ₜ (I × C64) :=
  (if reverse then unitInterval.symmHomeomorph else Homeomorph.refl I).prodCongr
    (Homeomorph.refl C64)

theorem annulusTargetReflection_involutive (reverse : Bool) (x : I × C64) :
    annulusTargetReflection reverse (annulusTargetReflection reverse x) = x := by
  cases reverse <;> simp [annulusTargetReflection]
  rcases x with ⟨t, z⟩
  exact Prod.ext (unitInterval.symm_symm t) rfl

theorem exists_relative_annulus_covering_of_opposite_rims
    (f : C(Ann, I × C64)) (g : C(C32, C64)) (hg : IsCoveringMap g)
    (U : C32 ≃ₜ C32) (L : (ContinuousMap.id C32).Homotopy (U : C(C32, C32)))
    (hlift : ∀ t z, g (L (t, z)) = (f (annulusCylinderHomeomorph (t, z))).2)
    (label : Bool → Bool) (hdiff : label false ≠ label true)
    (hnormal : ∀ side z, (f (annulusRimPoint side z)).1 = if label side then 1 else 0)
    (A : Ann ≃ₜ Ann) (hA : A.IsFinitePL)
    (hA0 : ∀ z, A (annulusRimPoint false z) = annulusRimPoint false z)
    (hA1 : ∀ z, A (annulusRimPoint true z) = annulusRimPoint true (U z)) :
    ∃ D : Ann ≃ₜ Ann, D.IsFinitePL ∧
      ∃ c : C(Ann, I × C64), IsCoveringMap c ∧
        (∀ x, c x = annulusTargetReflection (label false)
          ((annulusCylinderHomeomorph.symm (D x)).1,
            g (annulusCylinderHomeomorph.symm (D x)).2)) ∧
        Nonempty (f.HomotopyRel c annulusRims) := by
  let R := annulusTargetReflection (label false)
  let reflected := (R : C(I × C64, I × C64)).comp f
  have hrims (side : Bool) (z : C32) :
      (reflected (annulusRimPoint side z)).1 = if side then 1 else 0 := by
    change (R (f (annulusRimPoint side z))).1 = _
    change ((if label false then unitInterval.symmHomeomorph else Homeomorph.refl I)
      (f (annulusRimPoint side z)).1) = _
    rw [hnormal]
    cases side <;> cases h0 : label false <;> cases h1 : label true <;>
      simp_all
  obtain ⟨D, hD, c, hc, hformula, ⟨H⟩⟩ :=
    exists_relative_annulus_covering_of_rim_extension reflected g hg U L hlift hrims
      A hA hA0 hA1
  let result := (R : C(I × C64, I × C64)).comp c
  have hresult : IsCoveringMap result := hc.homeomorph_comp R
  have hinvol : (R : C(I × C64, I × C64)).comp reflected = f := by
    apply ContinuousMap.ext
    intro x
    exact annulusTargetReflection_involutive _ (f x)
  exact ⟨D, hD, result, hresult, fun x => congrArg R (hformula x),
    ⟨(H.compContinuousMap (R : C(I × C64, I × C64))).cast hinvol rfl⟩⟩

end PoincareConjecture.M76.Dehn
