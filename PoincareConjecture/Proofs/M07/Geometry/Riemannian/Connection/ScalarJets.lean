import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.M07.Analysis.NormedSpace.FiniteDimension








set_option autoImplicit false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Topology
open Filter

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ}



theorem iteratedFDeriv_inner_eq
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x a b : EuclideanSpace ℝ (Fin n)) (r : ℕ)
    (v : Fin r → EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ r (fun y => g.inner y a b) x v =
      (iteratedFDeriv ℝ r g.euclideanCoefficients x v) a b := by
  let E := EuclideanSpace ℝ (Fin n)
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)
  have hr : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change (↑(r : ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have h := ev.iteratedFDeriv_comp_left (g.contDiffAt_euclideanCoefficients x) hr
  have hh := congrArg (fun A => A v) h
  change iteratedFDeriv ℝ r (fun y => g.inner y a b) x v =
    (iteratedFDeriv ℝ r g.euclideanCoefficients x v) a b at hh
  exact hh



theorem tendsto_euclideanCoefficients_of_scalar_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)) ∧
    Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)) ∧
    Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x)) := by
  have hev (r : ℕ) (hr : r ≤ 2) (a c : ι)
      (v : Fin r → EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun i => (iteratedFDeriv ℝ r (gseq i).euclideanCoefficients x v)
        (b a) (b c)) l
        (𝓝 ((iteratedFDeriv ℝ r g.euclideanCoefficients x v) (b a) (b c))) := by
    have hh := (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin r => EuclideanSpace ℝ (Fin n)) ℝ v).continuous.continuousAt.tendsto.comp
        (h r hr a c)
    simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply,
      iteratedFDeriv_inner_eq] using hh
  refine ⟨?_, ?_, ?_⟩
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa using hev 0 (by omega) a c (fun i => Fin.elim0 i)
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro u
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa using hev 1 (by omega) a c (fun _ => b u)
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro u
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro v
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa [iteratedFDeriv_two_apply] using
      hev 2 (by omega) a c (fun j => if j = 0 then b u else b v)

end PoincareConjecture.RiemannianMetric
