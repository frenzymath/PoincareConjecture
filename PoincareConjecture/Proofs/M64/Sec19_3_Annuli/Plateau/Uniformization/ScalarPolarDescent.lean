import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarLocal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarInverseFibers
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalarCoverMap_surjective_of_ne_zero {p : Plane} (hp : p ≠ 0) :
    ∃ z : Cover, 0 < z.1 ∧ scalarCoverMap z = p := by
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hunit : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp0.le), inv_mul_cancel₀ hp0.ne']
  obtain ⟨t, -, ht⟩ := Proofs.M58.exists_angularPoint ⟨‖p‖⁻¹ • p, hunit⟩
  refine ⟨(‖p‖, t / (2 * Real.pi)), hp0, ?_⟩
  rw [scalarCoverMap_polar_relation, ht, smul_inv_smul₀ hp0.ne']

theorem scalarCoverMap_fiber_of_pos {z w : Cover} (hz : 0 < z.1) (hw : 0 < w.1)
    (heq : scalarCoverMap z = scalarCoverMap w) :
    ∃ k : ℤ, z = w + (0, (k : ℝ)) := by
  have hr : z.1 = w.1 := by
    have h := congrArg norm heq
    simpa only [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos hz, abs_of_pos hw] using h
  have hcos : Real.cos (2 * Real.pi * z.2) = Real.cos (2 * Real.pi * w.2) := by
    apply mul_left_cancel₀ hw.ne'
    have h := congrArg (fun p : Plane => p 0) heq
    simpa [scalarCoverMap, scalarCirclePoint, EuclideanSpace.basisFun_apply, hr] using h
  have hsin : Real.sin (2 * Real.pi * z.2) = Real.sin (2 * Real.pi * w.2) := by
    apply mul_left_cancel₀ hw.ne'
    have h := congrArg (fun p : Plane => p 1) heq
    simpa [scalarCoverMap, scalarCirclePoint, EuclideanSpace.basisFun_apply, hr] using h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    (Real.Angle.cos_sin_inj hcos hsin)
  refine ⟨k, Prod.ext (by simpa using hr) ?_⟩
  change z.2 = w.2 + (k : ℝ)
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  linear_combination hk

theorem scalarCoverMap_exists_smooth_localInverse {z : Cover} (hz : z.1 ≠ 0) :
    ∃ q : Plane → Cover, ContDiffAt ℝ ∞ q (scalarCoverMap z) ∧
      q (scalarCoverMap z) = z ∧ ∀ᶠ p in 𝓝 (scalarCoverMap z), scalarCoverMap (q p) = p := by
  obtain ⟨A, hA⟩ := scalarCoverMap_fderiv_invertible hz
  have hD : HasFDerivAt scalarCoverMap (A : Cover →L[ℝ] Plane) z := by
    rw [hA]
    exact (scalarCoverMap_smooth.differentiable (by simp) z).hasFDerivAt
  have hC := scalarCoverMap_smooth.contDiffAt (x := z)
  let q := hC.localInverse hD (by simp)
  refine ⟨q, hC.to_localInverse hD (by simp), hC.localInverse_apply_image hD (by simp), ?_⟩
  exact (hC.hasStrictFDerivAt' hD (by simp)).eventually_right_inverse

theorem scalar_exists_periodic_cover_descent {Y : Type*} (f : Cover → Y)
    (hperiod : ∀ r t : ℝ, f (r, t + 1) = f (r, t)) :
    ∃ F : Plane → Y, ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f z := by
  classical
  have hsurj (p : Plane) (hp : p ≠ 0) : ∃ z : Cover, 0 < z.1 ∧ scalarCoverMap z = p :=
    scalarCoverMap_surjective_of_ne_zero hp
  choose lift hpos hproject using hsurj
  let F : Plane → Y := fun p => if hp : p ≠ 0 then f (lift p hp) else f (1, 0)
  refine ⟨F, ?_⟩
  intro z hz
  have hp : scalarCoverMap z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa only [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos hz] using hz.ne'
  dsimp only [F]
  rw [dif_pos hp]
  obtain ⟨k, hk⟩ := scalarCoverMap_fiber_of_pos hz (hpos _ hp) (hproject _ hp).symm
  have h : Function.Periodic (fun t : ℝ => f ((lift (scalarCoverMap z) hp).1, t)) 1 :=
    fun t => hperiod _ t
  have hh := (h.int_mul k) (lift (scalarCoverMap z) hp).2
  calc
    f (lift (scalarCoverMap z) hp) = f (lift (scalarCoverMap z) hp + (0, (k : ℝ))) := by
      change f (lift (scalarCoverMap z) hp) =
        f ((lift (scalarCoverMap z) hp).1 + 0, (lift (scalarCoverMap z) hp).2 + (k : ℝ))
      simpa only [add_zero, mul_one, Prod.eta] using hh.symm
    _ = f z := congrArg f hk.symm

theorem scalarCoverDescent_local_germ {Y : Type*} {f : Cover → Y} {F : Plane → Y}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f z)
    {z : Cover} (hz : 0 < z.1) :
    ∃ q : Plane → Cover, ContDiffAt ℝ ∞ q (scalarCoverMap z) ∧
      q (scalarCoverMap z) = z ∧ F =ᶠ[𝓝 (scalarCoverMap z)] f ∘ q := by
  obtain ⟨q, hq, hqz, hright⟩ := scalarCoverMap_exists_smooth_localInverse hz.ne'
  have hpositive : ∀ᶠ p in 𝓝 (scalarCoverMap z), 0 < (q p).1 :=
    ((continuous_fst.continuousAt.comp hq.continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds (by simpa only [Function.comp_apply, hqz] using hz)))
  refine ⟨q, hq, hqz, ?_⟩
  filter_upwards [hright, hpositive] with p hp hpos
  exact (congrArg F hp.symm).trans (hdesc _ hpos)

theorem scalarCoverDescent_continuousOn {Y : Type*} [TopologicalSpace Y]
    {f : Cover → Y} {F : Plane → Y} (hf : Continuous f)
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f z) :
    ContinuousOn F {p | p ≠ 0} := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjective_of_ne_zero hp
  obtain ⟨q, hq, -, heq⟩ := scalarCoverDescent_local_germ hdesc hz
  exact ((hf.continuousAt.comp hq.continuousAt).congr_of_eventuallyEq heq).continuousWithinAt

theorem scalarCoverDescent_locallyLipschitzOn {Y : Type*} [PseudoEMetricSpace Y]
    {f : Cover → Y} {F : Plane → Y} (hf : LocallyLipschitz f)
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f z) :
    ∀ p : Plane, p ≠ 0 → ∃ L : ℝ≥0, ∃ V ∈ 𝓝 p, LipschitzOnWith L F V := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjective_of_ne_zero hp
  obtain ⟨q, hq, hqz, heq⟩ := scalarCoverDescent_local_germ hdesc hz
  obtain ⟨L, U, hU, hL⟩ := hf z
  obtain ⟨B, V, hV, hB⟩ := (hq.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  have hpre : q ⁻¹' U ∈ 𝓝 (scalarCoverMap z) :=
    hq.continuousAt.preimage_mem_nhds (hqz.symm ▸ hU)
  let W := V ∩ q ⁻¹' U ∩ {p | F p = (f ∘ q) p}
  refine ⟨L * B, W, inter_mem (inter_mem hV hpre) heq, ?_⟩
  have hcomp : LipschitzOnWith (L * B) (f ∘ q) W :=
    hL.comp (hB.mono (fun _ hx => hx.1.1)) (fun _ hx => hx.1.2)
  intro x hx y hy
  have hxvalue : F x = (f ∘ q) x := hx.2
  have hyvalue : F y = (f ∘ q) y := hy.2
  rw [hxvalue, hyvalue]
  exact hcomp hx hy

theorem scalarCoverDescent_contMDiffAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {f : Cover → M} {F : Plane → M}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = f z)
    {z : Cover} (hz : 0 < z.1) (hf : ContMDiffAt 𝓘(ℝ, Cover) (𝓡 n) 1 f z) :
    ContMDiffAt (𝓡 2) (𝓡 n) 1 F (scalarCoverMap z) := by
  obtain ⟨q, hq, hqz, heq⟩ := scalarCoverDescent_local_germ hdesc hz
  have hqm : ContMDiffAt (𝓡 2) 𝓘(ℝ, Cover) 1 q (scalarCoverMap z) :=
    contMDiffAt_iff_contDiffAt.mpr (hq.of_le (by simp))
  have hfm : ContMDiffAt 𝓘(ℝ, Cover) (𝓡 n) 1 f (q (scalarCoverMap z)) := hqz.symm ▸ hf
  exact (hfm.comp _ hqm).congr_of_eventuallyEq heq

end PoincareConjecture.M64Uniformization
