import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorptionInverse
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

noncomputable def sphereIsotopyAbsorption
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (UnitTwoSphere × ℝ) (UnitTwoSphere × ℝ) ∞ := by
  let T := sphereIsotopyTrackDiffeomorph hF hFt
  have htime : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun p : UnitTwoSphere × ℝ => (χ p.2, p.1)) :=
    (hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst
  refine
    { toFun := fun p => (F (χ p.2) p.1, p.2)
      invFun := fun p => ((T.symm (χ p.2, p.1)).2, p.2)
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := (hF.comp htime).prodMk contMDiff_snd
      contMDiff_invFun :=
        (contMDiff_snd.comp (T.symm.contMDiff.comp htime)).prodMk contMDiff_snd }
  · intro p
    apply Prod.ext
    · exact congrArg Prod.snd (T.symm_apply_apply (χ p.2, p.1))
    · rfl
  · intro p
    apply Prod.ext
    · have h := congrArg Prod.snd (T.apply_symm_apply (χ p.2, p.1))
      simpa only [T, sphereIsotopyTrackDiffeomorph_apply,
        sphereIsotopyTrackDiffeomorph_symm_fst] using h
    · rfl

@[simp] theorem sphereIsotopyAbsorption_apply
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : UnitTwoSphere × ℝ) :
    sphereIsotopyAbsorption hF hFt χ hχ p = (F (χ p.2) p.1, p.2) := rfl

@[simp] theorem sphereIsotopyAbsorption_symm_snd
    {F : ℝ → UnitTwoSphere → UnitTwoSphere}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => F p.1 p.2))
    (hFt : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, g q = F t q)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (p : UnitTwoSphere × ℝ) :
    ((sphereIsotopyAbsorption hF hFt χ hχ).symm p).2 = p.2 := rfl

noncomputable def collarCutoff (a b s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a) / (b - a))

theorem contDiff_collarCutoff (a b : ℝ) : ContDiff ℝ ∞ (collarCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem collarCutoff_mem_Icc (a b s : ℝ) : collarCutoff a b s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem collarCutoff_eq_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) :
    collarCutoff a b s = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hab).le)

theorem collarCutoff_eq_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) :
    collarCutoff a b s = 1 :=
  Real.smoothTransition.one_of_one_le
    ((one_le_div (sub_pos.mpr hab)).mpr (sub_le_sub_right hs a))

namespace DiffSphereIsotopyData

variable {f : UnitTwoSphere → UnitTwoSphere} (D : DiffSphereIsotopyData f)

noncomputable def collarDiffeomorph (a b : ℝ) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (UnitTwoSphere × ℝ) (UnitTwoSphere × ℝ) ∞ :=
  sphereIsotopyAbsorption D.isotopy_smooth D.isotopy_diffeo
    (collarCutoff a b) (contDiff_collarCutoff a b)

@[simp] theorem collarDiffeomorph_apply (a b : ℝ) (p : UnitTwoSphere × ℝ) :
    D.collarDiffeomorph a b p = (D.isotopy (collarCutoff a b p.2) p.1, p.2) := rfl

theorem collarDiffeomorph_eq_isometry {a b : ℝ} (hab : a < b)
    (p : UnitTwoSphere × ℝ) (hp : p.2 ≤ a) :
    D.collarDiffeomorph a b p = (sphereMap D.isometry p.1, p.2) := by
  rw [D.collarDiffeomorph_apply, collarCutoff_eq_zero hab hp, D.isotopy_zero]

theorem collarDiffeomorph_eq_map {a b : ℝ} (hab : a < b)
    (p : UnitTwoSphere × ℝ) (hp : b ≤ p.2) :
    D.collarDiffeomorph a b p = (f p.1, p.2) := by
  rw [D.collarDiffeomorph_apply, collarCutoff_eq_one hab hp, D.isotopy_one]

@[simp] theorem collarDiffeomorph_symm_snd (a b : ℝ) (p : UnitTwoSphere × ℝ) :
    ((D.collarDiffeomorph a b).symm p).2 = p.2 := rfl

end DiffSphereIsotopyData

end PoincareConjecture.M25.Topology3D
