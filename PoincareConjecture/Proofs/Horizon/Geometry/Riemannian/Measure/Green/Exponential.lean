import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Rademacher
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem integral_exp_neg_mul_laplacian_of_locally_lipschitz
    (D : LeviCivitaData g) {l φ : M → ℝ} (hl : Continuous l)
    (hlocal : ∀ a : M, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (l ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) O)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => Real.exp (-l x) *
      g.inner x (D.gradient l x) (D.gradient φ x)) g.volumeMeasure ∧
    (∫ x, Real.exp (-l x) * D.laplacian φ x ∂g.volumeMeasure) =
      ∫ x, Real.exp (-l x) * g.inner x (D.gradient l x) (D.gradient φ x)
        ∂g.volumeMeasure := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : SigmaCompactSpace M := inferInstance
  have hF : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-s)) := Real.contDiff_exp.comp contDiff_neg
  have hcomp := locally_lipschitz_coordinates_comp (hF.of_le (by simp)).locallyLipschitz hlocal
  have hcont : Continuous (fun x => Real.exp (-l x)) := hl.neg.rexp
  obtain ⟨hi, heq⟩ := D.integral_mul_laplacian_of_locally_lipschitz hcont hcomp hφ hc
  have hp : (fun x => mvfderiv (𝓡 n) (fun y => Real.exp (-l y)) x (D.gradient φ x)) =ᵐ[g.volumeMeasure]
      (fun x => -(Real.exp (-l x) * g.inner x (D.gradient l x) (D.gradient φ x))) := by
    filter_upwards [g.ae_mDifferentiableAt_of_locally_lipschitz hlocal] with x hx
    have hd : deriv (fun s : ℝ => Real.exp (-s)) (l x) = -Real.exp (-l x) := by
      simpa [Function.comp_def] using
        ((Real.hasDerivAt_exp (-l x)).comp (l x) (hasDerivAt_id (l x)).neg).deriv
    rw [← D.inner_gradient]
    have hgrad := D.gradient_comp hx (hF.differentiable (by simp) (l x))
    simp only [Function.comp_def] at hgrad
    rw [hgrad, hd]
    simp only [map_smul, smul_apply, smul_eq_mul, neg_mul]
  have hi' := (hi.congr hp).neg
  have hi'' : Integrable (fun x => -(-(Real.exp (-l x) *
      g.inner x (D.gradient l x) (D.gradient φ x)))) g.volumeMeasure := hi'
  refine ⟨by simpa only [neg_neg] using hi'', ?_⟩
  rw [heq, integral_congr_ae hp, integral_neg, neg_neg]

end PoincareConjecture.LeviCivitaData
