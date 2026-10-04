import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Limits.MultilinearBasisConvergence
import PoincareLib.Geometry.Riemannian.Connection.ScalarJets

/-!
# Full metric jets from scalar coefficients at every order

Finite basis evaluation detects the multilinear operator topology, and
spatial differentiation commutes with its two output evaluations. This
recovers actual coefficient jets for Morgan-Tian Theorem 12.28,
pp. 323-324; see included-cylinder-geometric-readouts.md.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

/-- Scalar basis coefficients control the full coefficient derivative
at any finite order, for arbitrary filters (Theorem 12.28). -/
theorem tendsto_iteratedFDeriv_euclideanCoefficients_of_scalar_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (r : ℕ) (x : EuclideanSpace ℝ (Fin n)) {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ a c : ι, Tendsto (fun i => iteratedFDeriv ℝ r
      (fun y => (gseq i).inner y (b a) (b c)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (gseq i).euclideanCoefficients x) l
      (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x)) := by
  let := Fintype.ofFinite ι
  apply ContinuousMultilinearMap.tendsto_of_basis (fun _ => b)
  intro v
  apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
  intro a
  apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
  intro c
  have hh := (ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin r => EuclideanSpace ℝ (Fin n)) ℝ
      (fun i => b (v i))).continuous.continuousAt.tendsto.comp
      (h a c)
  simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_inner_eq] using hh

end PoincareMT.RiemannianMetric
