import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereFixedDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sphereInterpolation (f : E → E) (p : ℝ × E) : ℝ × E :=
  (p.1, p.2 + Real.smoothTransition p.1 • (f p.2 - p.2))

theorem sphereInterpolation_fixed (f : E → E) (t : ℝ) {x : E} (hx : f x = x) :
    sphereInterpolation f (t, x) = (t, x) := by
  simp only [sphereInterpolation, hx, sub_self, smul_zero, add_zero]

theorem sphereInterpolation_zero (f : E → E) (x : E) :
    sphereInterpolation f (0, x) = (0, x) := by
  simp only [sphereInterpolation, Real.smoothTransition.zero_of_nonpos le_rfl,
    zero_smul, add_zero]

theorem sphereInterpolation_one (f : E → E) (x : E) :
    sphereInterpolation f (1, x) = (1, f x) := by
  simp only [sphereInterpolation, Real.smoothTransition.one_of_one_le le_rfl,
    one_smul, add_sub_cancel]

theorem sphereInterpolation_contDiffOn (f : E → E) {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (sphereInterpolation f) (univ ×ˢ U) := by
  exact contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).contDiffOn.smul
      ((hf.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).sub
        contDiff_snd.contDiffOn)))

theorem sphereInterpolation_hasFDerivAt (f : E → E) (t : ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : f x = x) :
    HasFDerivAt (sphereInterpolation f)
      ((ContinuousLinearMap.id ℝ ℝ).prodMap
        ((1 - Real.smoothTransition t) • ContinuousLinearMap.id ℝ E +
          Real.smoothTransition t • fderiv ℝ f x)) (t, x) := by
  have hs : HasFDerivAt (@Prod.snd ℝ E) (ContinuousLinearMap.snd ℝ ℝ E) (t, x) :=
    hasFDerivAt_snd
  have ht : HasFDerivAt (@Prod.fst ℝ E) (ContinuousLinearMap.fst ℝ ℝ E) (t, x) :=
    hasFDerivAt_fst
  have ha := (((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp)) t).hasFDerivAt
  have hd := ht.prodMk (hs.fun_add ((ha.comp (t, x) ht).fun_smul
    ((hf.hasFDerivAt.comp (t, x) hs).fun_sub hs)))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext
  · rfl
  · change p.2 + (Real.smoothTransition t • (fderiv ℝ f x p.2 - p.2) +
        (fderiv ℝ Real.smoothTransition t p.1) • (f x - x)) =
      (1 - Real.smoothTransition t) • p.2 + Real.smoothTransition t • fderiv ℝ f x p.2
    rw [hx, sub_self, smul_zero, add_zero]
    module

theorem sphereInterpolation_invertible_derivative [FiniteDimensional ℝ E]
    (f : E → E) (t : ℝ) {x : E} (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x)
    (hfixed : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → f y = y)
    (hn : 0 < ⟪x, fderiv ℝ f x x⟫_ℝ) :
    ∃ A : (ℝ × E) ≃L[ℝ] (ℝ × E),
      HasFDerivAt (sphereInterpolation f) (A : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x) := by
  have htan := fun v hv => fderiv_eq_of_local_fixed_sphere f x v hx hf hfixed hv
  obtain ⟨B, hB⟩ := fixedHyperplane_interpolation_isUnit (fderiv ℝ f x) x hx htan hn
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  let A := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.ofUnit B)
  refine ⟨A, ?_⟩
  change HasFDerivAt (sphereInterpolation f)
    ((ContinuousLinearMap.id ℝ ℝ).prodMap (B : E →L[ℝ] E)) (t, x)
  rw [hB]
  exact sphereInterpolation_hasFDerivAt f t hf (hfixed.self_of_nhds hx)

theorem exists_sphereInterpolation_chart [FiniteDimensional ℝ E]
    (f : E → E) {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hfixed : ∀ x ∈ sphere (0 : E) 1, f x = x)
    (hn : ∀ x ∈ sphere (0 : E) 1, 0 < ⟪x, fderiv ℝ f x x⟫_ℝ)
    (a b : ℝ) :
    ∃ e : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
      (e : (ℝ × E) → (ℝ × E)) = sphereInterpolation f ∧
      Icc a b ×ˢ sphere (0 : E) 1 ⊆ e.source ∧ e.source ⊆ univ ×ˢ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  apply exists_smoothChart_near_compact (sphereInterpolation f)
    (isCompact_Icc.prod (isCompact_sphere _ _)) (isOpen_univ.prod hU)
    (fun _ hp => ⟨mem_univ _, hSU hp.2⟩) (sphereInterpolation_contDiffOn f hf)
  · intro p hp q hq hpq
    rw [sphereInterpolation_fixed f p.1 (hfixed p.2 hp.2),
      sphereInterpolation_fixed f q.1 (hfixed q.2 hq.2)] at hpq
    exact hpq
  · intro p hp
    apply sphereInterpolation_invertible_derivative f p.1
      (mem_sphere_zero_iff_norm.mp hp.2)
      ((hf.contDiffAt (hU.mem_nhds (hSU hp.2))).differentiableAt (by simp))
      (Filter.Eventually.of_forall fun y hy => hfixed y (mem_sphere_zero_iff_norm.mpr hy))
      (hn p.2 hp.2)

end PoincareConjecture.M25.Topology3D
