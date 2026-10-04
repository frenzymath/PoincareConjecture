import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.CollarAbsorptionInverse
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Absorbing the supplied sphere isotopy into a collar

The sphere isotopy used in Morgan--Tian Corollary 15.4(2), p. 358, gives a
global cylinder diffeomorphism preserving the height coordinate. A smooth
cutoff makes it the orthogonal endpoint below a chosen interval and the
prescribed sphere map above that interval. The inverse is jointly smooth
by the parameter-preserving track theorem.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M74

open M25.Topology3D

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "ITrack" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 2)

/-- A smooth height cutoff with constant values outside its transition
interval (MT Corollary 15.4(2), p. 358). -/
noncomputable def collarCutoff (a b s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a) / (b - a))

/-- The cutoff is smooth even when the endpoints coincide; endpoint
identities will separately assume their strict order (MT Corollary 15.4(2), p. 358). -/
theorem contDiff_collarCutoff (a b : ℝ) : ContDiff ℝ ∞ (collarCutoff a b) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))

/-- The cutoff always stays in the service's endpoint parameter interval
(MT Corollary 15.4(2), p. 358). -/
theorem collarCutoff_mem_Icc (a b s : ℝ) : collarCutoff a b s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The lower part of the collar uses isotopy time zero
(MT Corollary 15.4(2), p. 358). -/
theorem collarCutoff_eq_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) :
    collarCutoff a b s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hab).le

/-- The upper part of the collar uses isotopy time one
(MT Corollary 15.4(2), p. 358). -/
theorem collarCutoff_eq_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) :
    collarCutoff a b s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (sub_pos.mpr hab)).mpr
  exact sub_le_sub_right hs a

/-- Evaluating a smooth sphere isotopy at a smooth height function gives
a diffeomorphism preserving each cylinder level (MT Corollary 15.4(2), p. 358). -/
noncomputable def absorbSphereIsotopy
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞ := by
  let T := sphereIsotopyTrackDiffeomorph hF hFt
  let input : RoundCylinderSpace → ℝ × UnitTwoSphere := fun p => (χ p.2, p.1)
  have hinput : ContMDiff ICollar ITrack ∞ input :=
    (hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst
  refine {
    toFun := fun p => (F (χ p.2) p.1, p.2)
    invFun := fun p => ((T.symm (input p)).2, p.2)
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := (hF.comp hinput).prodMk contMDiff_snd
    contMDiff_invFun :=
      (contMDiff_snd.comp (T.symm.contMDiff.comp hinput)).prodMk contMDiff_snd }
  · rintro ⟨q, s⟩
    apply Prod.ext
    · exact congrArg Prod.snd (T.symm_apply_apply (χ s, q))
    · rfl
  · rintro ⟨q, s⟩
    apply Prod.ext
    · have h := congrArg Prod.snd (T.apply_symm_apply (χ s, q))
      change F (T.symm (χ s, q)).1 (T.symm (χ s, q)).2 = q at h
      rw [sphereIsotopyTrackDiffeomorph_symm_fst] at h
      exact h
    · rfl

/-- The absorption map changes only the sphere coordinate
(MT Corollary 15.4(2), p. 358). -/
@[simp] theorem absorbSphereIsotopy_apply
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : RoundCylinderSpace) :
    absorbSphereIsotopy hF hFt χ hχ p = (F (χ p.2) p.1, p.2) := rfl

/-- The inverse absorption map also leaves height unchanged
(MT Corollary 15.4(2), p. 358). -/
@[simp] theorem absorbSphereIsotopy_symm_snd
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : RoundCylinderSpace) :
    ((absorbSphereIsotopy hF hFt χ hχ).symm p).2 = p.2 := rfl

/-- A service datum supplies a collar diffeomorphism joining its two
sphere-map endpoints (MT Corollary 15.4(2), p. 358). -/
noncomputable def collarDiffeomorph {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) :
    Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞ :=
  absorbSphereIsotopy D.isotopy_smooth D.isotopy_diffeo
    (collarCutoff a b) (contDiff_collarCutoff a b)

/-- The service-based collar map has its literal isotopy formula
(MT Corollary 15.4(2), p. 358). -/
@[simp] theorem collarDiffeomorph_apply {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) (p : RoundCylinderSpace) :
    collarDiffeomorph D a b p = (D.isotopy (collarCutoff a b p.2) p.1, p.2) := rfl

/-- The lower collar agrees with the orthogonal endpoint, allowing either
orientation (MT Corollary 15.4(2), p. 358). -/
theorem collarDiffeomorph_eq_isometry {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) {a b : ℝ} (hab : a < b)
    (p : RoundCylinderSpace) (hp : p.2 ≤ a) :
    collarDiffeomorph D a b p = (sphereMap D.isometry p.1, p.2) := by
  rw [collarDiffeomorph_apply, collarCutoff_eq_zero hab hp, D.isotopy_zero]

/-- The upper collar agrees with the prescribed sphere diffeomorphism
(MT Corollary 15.4(2), p. 358). -/
theorem collarDiffeomorph_eq_map {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) {a b : ℝ} (hab : a < b)
    (p : RoundCylinderSpace) (hp : b ≤ p.2) :
    collarDiffeomorph D a b p = (f p.1, p.2) := by
  rw [collarDiffeomorph_apply, collarCutoff_eq_one hab hp, D.isotopy_one]

/-- The service-based inverse preserves every collar level exactly
(MT Corollary 15.4(2), p. 358). -/
@[simp] theorem collarDiffeomorph_symm_snd {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) (p : RoundCylinderSpace) :
    ((collarDiffeomorph D a b).symm p).2 = p.2 := rfl

end PoincareMT.M74
