import PoincareConjecture.Proofs.M25.Topology3D.Space3.CirclePeriodCoordinates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring








set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem circleAffine_smooth_immersion (a v : ℝ) (hv : v ≠ 0) :
    let g : ℝ → UnitCircle := fun t =>
      complexUnitCircleHomeomorph (Circle.exp (a + v * t))
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ g ∧
      ∀ t : ℝ, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g t) := by
  let g : ℝ → UnitCircle := fun t =>
    complexUnitCircleHomeomorph (Circle.exp (a + v * t))
  let c : UnitCircle → ℂ := fun z => (complexUnitCircleHomeomorph.symm z : ℂ)
  let z : ℝ → ℂ := fun t => Complex.exp (((a + v * t : ℝ) : ℂ) * Complex.I)
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ g :=
    complexUnitCircleHomeomorph_contMDiff.comp
      (contMDiff_circleExp.comp ((contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff))
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ c := by
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
    exact (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp
      complexUnitCircleHomeomorph_symm_contMDiff
  have hcg : c ∘ g = z := by
    funext t
    simp only [comp_apply, c, g, Homeomorph.symm_apply_apply, Circle.coe_exp, z]
  refine ⟨hg, ?_⟩
  intro t
  have ha : HasDerivAt (fun s : ℝ => a + v * s) v t := by
    simpa using ((hasDerivAt_id t).const_mul v).const_add a
  have hreal : HasDerivAt (fun s : ℝ => ((a + v * s : ℝ) : ℂ)) (v : ℂ) t := by
    convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ha using 1
  have hz : HasDerivAt z (z t * ((v : ℂ) * Complex.I)) t := by
    simpa only [z] using (hreal.mul_const Complex.I).cexp
  have hn : z t * ((v : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hv) Complex.I_ne_zero)
  have hi : Injective (fderiv ℝ z t) := by
    intro r s hrs
    simp only [fderiv_eq_smul_deriv, hz.deriv] at hrs
    exact smul_left_injective ℝ hn hrs
  have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) z t = fderiv ℝ z t :=
    hz.differentiableAt.hasFDerivAt.hasMFDerivAt.mfderiv
  have hchain := (hc.mdifferentiable (by simp) (g t)).hasMFDerivAt.comp t
    (hg.mdifferentiable (by simp) t).hasMFDerivAt
  rw [hcg] at hchain
  have hcomp : Injective ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (g t)).comp
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g t)) := by
    rw [← hchain.mfderiv, hm]
    exact hi
  intro r s hrs
  exact hcomp (congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (g t)) hrs)



theorem circleAffine_injOn (a v l r : ℝ) (hv : v ≠ 0)
    (hwidth : |v| * (r - l) < 2 * Real.pi) :
    InjOn (fun t : ℝ => complexUnitCircleHomeomorph (Circle.exp (a + v * t))) (Icc l r) := by
  let A : Set ℝ := (fun t : ℝ => a + v * t) '' Icc l r
  have he : InjOn Circle.exp A := Circle.exp_injOn_of_forall_sub_mem_Ioo (by
    rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩
    have hts : |t - s| ≤ r - l := abs_le.mpr ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
    have hh : |(a + v * t) - (a + v * s)| < 2 * Real.pi := by
      have halg : (a + v * t) - (a + v * s) = v * (t - s) := by ring
      rw [halg, abs_mul]
      exact (mul_le_mul_of_nonneg_left hts (abs_nonneg v)).trans_lt hwidth
    change -2 * Real.pi < (a + v * t) - (a + v * s) ∧
      (a + v * t) - (a + v * s) < 2 * Real.pi
    exact ⟨by linarith only [(abs_lt.mp hh).1], (abs_lt.mp hh).2⟩)
  intro t ht s hs hts
  have hangle := he ⟨t, ht, rfl⟩ ⟨s, hs, rfl⟩
    (complexUnitCircleHomeomorph.injective hts)
  exact (mul_left_cancel₀ hv) (add_left_cancel hangle)



theorem exists_circleAffine_extension (a v : ℝ) (hv : 0 < |v|)
    (hvpi : |v| < 2 * Real.pi) :
    let g : ℝ → UnitCircle := fun t =>
      complexUnitCircleHomeomorph (Circle.exp (a + v * t))
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 8 ∧
      InjOn g (Icc (-eta) (1 + eta)) ∧
      (∀ t ∈ Ioo (-eta) (0 : ℝ), g t ∉ g '' Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Ioo (1 : ℝ) (1 + eta), g t ∉ g '' Icc (0 : ℝ) 1 := by
  let g : ℝ → UnitCircle := fun t =>
    complexUnitCircleHomeomorph (Circle.exp (a + v * t))
  let eta : ℝ := min (1 / 16) ((2 * Real.pi - |v|) / (8 * (|v| + 1)))
  have hp : 0 < eta := lt_min (by norm_num) (div_pos (sub_pos.mpr hvpi) (by positivity))
  have hu : eta ≤ 1 / 16 := min_le_left _ _
  have hd : eta * (8 * (|v| + 1)) ≤ 2 * Real.pi - |v| :=
    (le_div_iff₀ (by positivity : 0 < 8 * (|v| + 1))).mp (min_le_right _ _)
  have hi : InjOn g (Icc (-eta) (1 + eta)) :=
    circleAffine_injOn a v (-eta) (1 + eta) (abs_pos.mp hv) (by nlinarith)
  refine ⟨eta, hp, by linarith, hi, ?_, ?_⟩
  · intro t ht
    rintro ⟨s, hs, heq⟩
    have hst := hi (show s ∈ Icc (-eta) (1 + eta) from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show t ∈ Icc (-eta) (1 + eta) from ⟨ht.1.le, by linarith [ht.2]⟩) heq
    linarith [hs.1, ht.2]
  · intro t ht
    rintro ⟨s, hs, heq⟩
    have hst := hi (show s ∈ Icc (-eta) (1 + eta) from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show t ∈ Icc (-eta) (1 + eta) from ⟨by linarith [ht.1], ht.2.le⟩) heq
    linarith [hs.2, ht.1]

end PoincareConjecture.M25.Topology3D
