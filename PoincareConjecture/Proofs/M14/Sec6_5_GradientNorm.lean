import PoincareConjecture.Proofs.M14.Sec6_5_RegularSpatialDerivative
import PoincareConjecture.Statements.M14GeneralizedLGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_t2Space {q : G.Point} : T2Space (G.Horizontal q) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal q

attribute [local instance] horizontal_t2Space

theorem horizontal_inner_sum_sq (q : G.Point)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal q))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner q (b i) (b j) = if i = j then 1 else 0)
    (A : G.Horizontal q) :
    (∑ i, (G.spacetime.horizontalMetric.inner q A (b i)) ^ 2) =
      G.spacetime.horizontalMetric.inner q A A := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hbo : Orthonormal ℝ b := orthonormal_iff_ite.mpr hb
  have h := (b.toOrthonormalBasis hbo).sum_sq_inner_left A
  change (∑ i, (inner ℝ A (b i)) ^ 2) = inner ℝ A A
  simpa only [Module.Basis.coe_toOrthonormalBasis, real_inner_self_eq_norm_sq] using h

theorem reducedLengthGradientNormSq_eq_of_differential
    {T τ₁ : ℝ} (x q : G.Point) (b : Module.Basis (Fin n) ℝ (G.Horizontal q))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner q (b i) (b j) = if i = j then 1 else 0)
    (A : G.Horizontal q) (c : ℝ)
    (hd : ∀ V : G.Horizontal q,
      mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T τ₁ x) q V.val =
        G.spacetime.horizontalMetric.inner q A V / c) :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := τ₁) G x q b =
      G.spacetime.horizontalMetric.inner q A A / c ^ 2 := by
  unfold M14ReducedLengthGradientNormSq
  simp_rw [hd, div_pow]
  rw [← Finset.sum_div, horizontal_inner_sum_sq q b hb A]

private theorem inner_transport {q r : G.Point} (h : q = r) (A : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner r (h ▸ A) (h ▸ A) =
      G.spacetime.horizontalMetric.inner q A A := by
  cases h
  rfl

theorem reducedLengthGradientNormSq_eq_squareEnergy
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal (E.gamma Z s)))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner (E.gamma Z s) (b i) (b j) =
      if i = j then 1 else 0) :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x (E.gamma Z s) b =
      G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s)
        ((E.square_path Z s hs hpos).horizontal_velocity s)
        ((E.square_path Z s hs hpos).horizontal_velocity s) / (4 * s ^ 2) := by
  rw [reducedLengthGradientNormSq_eq_of_differential x (E.gamma Z s) b hb
    (hpoint ▸ (E.square_path Z s hs hpos).horizontal_velocity s) (2 * s)
    (reducedLengthAt_horizontal_differential hCoordinates hM04 hM12 E hs hpos hz hpoint),
    inner_transport hpoint]
  congr 1
  ring

end PoincareConjecture.M14
