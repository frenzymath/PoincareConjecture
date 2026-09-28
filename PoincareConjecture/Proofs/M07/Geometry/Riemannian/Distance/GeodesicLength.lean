import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Speed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isGeodesicOn_const (g : RiemannianMetric n M) (p : M) (s : Set ℝ) :
    g.IsGeodesicOn (fun _ : ℝ => p) s := by
  intro t _
  refine ⟨p, fun _ => extChartAt (𝓡 n) p p, fun _ => 0,
    Eventually.of_forall (fun u => ?_)⟩
  refine ⟨((extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)).symm,
    mem_extChartAt_target p, hasDerivAt_const u _, ?_⟩
  have hz : coordinateChristoffel
      (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      (extChartAt (𝓡 n) p p) 0 0 = 0 := by
    unfold coordinateChristoffel metricKoszulCovector
    simp only [map_zero, zero_add, zero_sub, smul_zero, neg_zero]
  rw [hz, neg_zero]
  exact hasDerivAt_const u (0 : EuclideanSpace ℝ (Fin n))

theorem pathELength_eq_of_tangentNorm_eq
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b,
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = C) :
    g.pathELength γ a b = ENNReal.ofReal C * ENNReal.ofReal (b - a) := by
  rw [pathELength_eq_lintegral_tangentNorm]
  have heq : (fun t => ENNReal.ofReal
      (g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1))) =ᵐ[
        volume.restrict (Icc a b)] fun _ => ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hC t ht]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Icc]

open scoped Bundle in

theorem exists_minimizing_constant_geodesic (g : RiemannianMetric n M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = p ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p p := by
  refine ⟨1, zero_lt_one, fun _ => p, g.isGeodesicOn_const p _, rfl, rfl, ?_⟩
  intro s _ t _
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [edist, Manifold.riemannianEDist_self, mul_zero]

end PoincareConjecture.RiemannianMetric
