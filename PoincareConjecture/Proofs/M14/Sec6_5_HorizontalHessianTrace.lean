import PoincareConjecture.Proofs.M14.Mathlib.HessianTrace
import PoincareConjecture.Statements.M14GeneralizedLGeometry









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem sliceLaplacian_eq_horizontal_hessian_trace {T τ : ℝ}
    (q : (G.slices (T - τ)).Point) (f : G.Point → ℝ)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun r : (G.slices (T - τ)).Point => f r.val) q)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal q.val))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner q.val (b i) (b j) =
      if i = j then 1 else 0) :
    (G.leafwise.sliceConnection (T - τ)).laplacian (fun r => f r.val) q =
      ∑ i, M14ReducedLengthHessianPairing G q f (b i) (b i) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (G.slices (T - τ)).Point :=
    (G.slices (T - τ)).chartedSpace
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : (G.slices (T - τ)).Point → Type _) :=
    ⟨(G.slices (T - τ)).metricOnPoints.toRiemannianMetric⟩
  let bs := b.map ((G.slices (T - τ)).tangentEquiv q).symm.toLinearEquiv
  have hbs : Orthonormal ℝ bs := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change (G.slices (T - τ)).metricOnPoints.inner q (bs i) (bs j) = _
    rw [(G.slices (T - τ)).metric_eq]
    simpa only [bs, Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply] using hb i j
  simpa only [Module.Basis.coe_toOrthonormalBasis, bs, Module.Basis.map_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, M14ReducedLengthHessianPairing] using
    laplacian_eq_orthonormal_hessian_trace (G.leafwise.sliceConnection (T - τ))
      (fun r => f r.val) q hf (bs.toOrthonormalBasis hbs)



theorem reducedLengthAt_slice_eq {T a τ : ℝ} (x : G.Point) :
    (fun q : (G.slices (T - τ)).Point => M14ReducedLengthAt G T a x q.val) =
      (fun q : (G.slices (T - τ)).Point => M14ReducedLengthValue G T a τ x q.val) := by
  funext q
  unfold M14ReducedLengthAt
  rw [q.property]
  congr 1
  ring




theorem reducedLengthLaplacian_eq_horizontal_hessian_trace {T a τ : ℝ}
    (x : G.Point) (q : (G.slices (T - τ)).Point)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun r : (G.slices (T - τ)).Point => M14ReducedLengthAt G T a x r.val) q)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal q.val))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner q.val (b i) (b j) =
      if i = j then 1 else 0) :
    M14ReducedLengthLaplacian (T := T) (τ₁ := a) G x q =
      ∑ i, M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T a x) (b i) (b i) := by
  have h := sliceLaplacian_eq_horizontal_hessian_trace q (M14ReducedLengthAt G T a x) hf b hb
  rw [reducedLengthAt_slice_eq] at h
  exact h

end PoincareConjecture.M14
