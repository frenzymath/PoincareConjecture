import PoincareConjecture.Proofs.M35.RadialGauge.HeatEquation
import PoincareConjecture.Proofs.M35.RadialGauge.JointJetContinuity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35LaplacianFamilyDualGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35LaplacianFamilyDualSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance m35LaplacianFamilyHessianGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35LaplacianFamilyHessianSpace :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem euclideanLaplacian_family_controls {u : A → V → ℝ}
    (hc : Continuous (fun p : A × V => u p.1 p.2))
    (hs : ∀ a, ContDiff ℝ ∞ (u a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C) :
    (∀ a, ContDiff ℝ ∞ (euclideanLaplacian (u a))) ∧
    Continuous (fun p : A × V => euclideanLaplacian (u p.1) p.2) ∧
    ∀ j : ℕ, ∃ C : ℝ, ∀ a x,
      ‖iteratedFDeriv ℝ j (euclideanLaplacian (u a)) x‖ ≤ C := by
  let e (i : Fin (n + 1)) := EuclideanSpace.single i (1 : ℝ)
  let tr : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (n + 1), (ContinuousLinearMap.apply ℝ ℝ (e i)).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (e i))
  have htr (B : V →L[ℝ] V →L[ℝ] ℝ) : tr B = ∑ i, B (e i) (e i) := by
    simp only [tr, _root_.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply]
  have heq (a : A) : euclideanLaplacian (u a) =
      tr ∘ fderiv ℝ (fderiv ℝ (u a)) := by
    funext x
    exact (htr _).symm
  have hds (a : A) := (contDiff_infty_iff_fderiv.mp (hs a)).2
  have hdds (a : A) := (contDiff_infty_iff_fderiv.mp (hds a)).2
  have hdb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (u a)) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hb (j + 1)
    exact ⟨C, fun a x => by rw [norm_iteratedFDeriv_fderiv]; exact hC a x⟩
  have hdc := spatial_fderiv_jointly_continuous_of_uniform_bounds hc hs hb
  have hddc := spatial_fderiv_jointly_continuous_of_uniform_bounds hdc hds hdb
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [heq]
    exact tr.contDiff.comp (hdds a)
  · simpa only [heq, Function.comp_def] using tr.continuous.comp hddc
  · intro j
    obtain ⟨C, hC⟩ := hb ((j + 1) + 1)
    refine ⟨‖tr‖ * C, fun a x => ?_⟩
    rw [heq]
    have h := tr.norm_iteratedFDeriv_comp_left (x := x) (hdds a).contDiffAt
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg tr)
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    exact hC a x

end PoincareConjecture.M35.RadialGauge
