import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGramDerivative
import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialJacobianNormalization
import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialJacobianTrace
import PoincareConjecture.Proofs.M10.JacobianEvolution
import PoincareConjecture.Proofs.M04

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponentialJacobian_hasDerivAt
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (b₀ : Module.Basis (Fin n) ℝ (G.Horizontal x))
    {Z : G.Horizontal x} {s b : ℝ} (hb : (Z, b) ∈ E.domain)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hlt : s < b)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    HasDerivAt (exponentialJacobian E b₀ Z)
      (2 * s * exponentialJacobian E b₀ Z s *
        (horizontalScalarCurvature G.leafwise (E.gamma Z s) +
          M14ReducedLengthLaplacian (τ₁ := 0) G x ⟨E.gamma Z s, E.clock Z s hs⟩)) s := by
  obtain ⟨C, e, he, hC⟩ := exists_exponentialJacobian_source_normalization E b₀ hs hpos hz
  let v : Fin n → G.Horizontal x := fun i => C (b₀ i)
  let A := exponentialGram E v Z
  let J := exponentialJacobian E b₀ Z
  obtain ⟨B, hA, hdiag⟩ := exponentialGram_hasDerivAt hCoordinates hM04 hM12 E v hb hs hpos hlt hz
  have hAt : A s = 1 := by
    ext i j
    change G.spacetime.horizontalMetric.inner (E.gamma Z s)
      (exponentialDifferential E Z s (C (b₀ i)))
      (exponentialDifferential E Z s (C (b₀ j))) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    rw [exponentialDifferential_eq E hs, hC, hC, he, Matrix.one_apply]
  have hscale : (fun r => |LinearMap.det C.toLinearMap| * J r) =ᶠ[𝓝 s]
      (fun r => Real.sqrt (A r).det) := by
    apply Eventually.of_forall
    intro r
    exact (exponentialJacobian_source_equiv E b₀ C Z r).symm.trans
      (exponentialJacobian_eq_sqrt_det E v Z r)
  let q : (G.slices (T - s ^ 2)).Point := ⟨E.gamma Z s, E.clock Z s hs⟩
  have hqimage : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) :=
    ⟨⟨(Z, s), hz⟩, rfl⟩
  have hRic := horizontalRicci_orthonormal_trace ricciFlowCurvatureTheory (E.gamma Z s) e he
  have hHess := reducedLengthLaplacian_eq_horizontal_hessian_trace x q
    (reducedLengthAt_slice_contMDiffAt hM04 hM12 E q hqimage) e he
  have hdiag' (i : Fin n) : B i i =
      4 * s * (horizontalRicci G.leafwise (E.gamma Z s) (e i) (e i) +
        M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x) (e i) (e i)) := by
    simpa only [v, hC] using hdiag i
  have htrace : B.trace / 2 = 2 * s *
      (horizontalScalarCurvature G.leafwise (E.gamma Z s) +
        M14ReducedLengthLaplacian (τ₁ := 0) G x q) := by
    change (∑ i, B i i) / 2 = _
    simp_rw [hdiag']
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hRic, ← hHess]
    ring
  have hd := M10.hasDerivAt_jacobian_of_scaled_normalized_gram
    (exponentialJacobian_source_factor_ne_zero C) hscale hA hAt
  rw [htrace] at hd
  convert hd using 1
  ring

end PoincareConjecture.M14
