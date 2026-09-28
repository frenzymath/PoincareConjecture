import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionInverse
import Mathlib.Analysis.SpecialFunctions.SmoothTransition











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M74

open M25.Topology3D

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "ITrack" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 2)



noncomputable def collarCutoff (a b s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a) / (b - a))



theorem contDiff_collarCutoff (a b : ℝ) : ContDiff ℝ ∞ (collarCutoff a b) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))



theorem collarCutoff_mem_Icc (a b s : ℝ) : collarCutoff a b s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩



theorem collarCutoff_eq_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) :
    collarCutoff a b s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hab).le



theorem collarCutoff_eq_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) :
    collarCutoff a b s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (sub_pos.mpr hab)).mpr
  exact sub_le_sub_right hs a



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



@[simp] theorem absorbSphereIsotopy_apply
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : RoundCylinderSpace) :
    absorbSphereIsotopy hF hFt χ hχ p = (F (χ p.2) p.1, p.2) := rfl



@[simp] theorem absorbSphereIsotopy_symm_snd
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff ITrack (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : RoundCylinderSpace) :
    ((absorbSphereIsotopy hF hFt χ hχ).symm p).2 = p.2 := rfl



noncomputable def collarDiffeomorph {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) :
    Diffeomorph ICollar ICollar RoundCylinderSpace RoundCylinderSpace ∞ :=
  absorbSphereIsotopy D.isotopy_smooth D.isotopy_diffeo
    (collarCutoff a b) (contDiff_collarCutoff a b)



@[simp] theorem collarDiffeomorph_apply {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) (p : RoundCylinderSpace) :
    collarDiffeomorph D a b p = (D.isotopy (collarCutoff a b p.2) p.1, p.2) := rfl



theorem collarDiffeomorph_eq_isometry {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) {a b : ℝ} (hab : a < b)
    (p : RoundCylinderSpace) (hp : p.2 ≤ a) :
    collarDiffeomorph D a b p = (sphereMap D.isometry p.1, p.2) := by
  rw [collarDiffeomorph_apply, collarCutoff_eq_zero hab hp, D.isotopy_zero]



theorem collarDiffeomorph_eq_map {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) {a b : ℝ} (hab : a < b)
    (p : RoundCylinderSpace) (hp : b ≤ p.2) :
    collarDiffeomorph D a b p = (f p.1, p.2) := by
  rw [collarDiffeomorph_apply, collarCutoff_eq_one hab hp, D.isotopy_one]



@[simp] theorem collarDiffeomorph_symm_snd {f : UnitTwoSphere → UnitTwoSphere}
    (D : DiffSphereIsotopyData f) (a b : ℝ) (p : RoundCylinderSpace) :
    ((collarDiffeomorph D a b).symm p).2 = p.2 := rfl

end PoincareConjecture.M74
