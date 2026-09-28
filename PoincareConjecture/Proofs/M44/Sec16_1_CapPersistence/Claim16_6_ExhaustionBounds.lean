import PoincareConjecture.Proofs.M36.StandardBalls
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Definitions.Ch12.StandardCap











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace




theorem exists_standard_ball_radius (g0 : StandardInitialMetric) (x : E) :
    ∃ R : ℝ, 0 < R ∧ x ∈ g0.metric.ball 0 R := by
  refine ⟨|M36.radialArclength g0 ‖x‖| + 1, by positivity, ?_⟩
  change g0.metric.edist 0 x < ENNReal.ofReal (|M36.radialArclength g0 ‖x‖| + 1)
  rw [M36.standard_edist_zero,
    ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < |M36.radialArclength g0 ‖x‖| + 1)]
  linarith only [le_abs_self (M36.radialArclength g0 ‖x‖)]




theorem curvature_bound_of_standard_exhaustion
    (g0 : StandardInitialMetric) {g : RiemannianMetric 3 E}
    (D : LeviCivitaData g) {K : ℝ}
    (hbound : ∀ R : ℝ, 0 < R → ∀ x ∈ g0.metric.ball 0 R,
      D.curvatureTensorNorm x ≤ K) (x : E) :
    |D.curvatureTensorNorm x| ≤ K := by
  obtain ⟨R, hR, hx⟩ := exists_standard_ball_radius g0 x
  have hnorm : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  rw [abs_of_nonneg hnorm]
  exact hbound R hR x hx






theorem curvature_bound_of_tendsto_on_standard_exhaustion
    (g0 : StandardInitialMetric) {J : Set ℝ}
    {g : ℝ → RiemannianMetric 3 E} (D : ∀ t, LeviCivitaData (g t))
    (q : ℕ → ℝ → E → ℝ) {K : ℝ}
    (hconv : ∀ t ∈ J, ∀ x,
      Tendsto (fun k => q k t x) atTop (𝓝 ((D t).curvatureTensorNorm x)))
    (hbound : ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ∀ t ∈ J, ∀ x ∈ g0.metric.ball 0 R, q k t x ≤ K) :
    ∀ t ∈ J, ∀ x : E, |(D t).curvatureTensorNorm x| ≤ K := by
  intro t ht x
  apply curvature_bound_of_standard_exhaustion g0 (D t) _ x
  intro R hR y hy
  exact le_of_tendsto (hconv t ht y)
    ((hbound R hR).mono fun k hk => hk t ht y hy)





theorem curvature_bound_of_metric_jets_on_standard_exhaustion
    (g0 : StandardInitialMetric) {J : Set ℝ}
    {g : ℝ → RiemannianMetric 3 E} (D : ∀ t, LeviCivitaData (g t))
    {gseq : ℕ → ℝ → RiemannianMetric 3 E}
    (Dseq : ∀ k t, LeviCivitaData (gseq k t)) {K : ℝ}
    (hjets : ∀ t ∈ J, ∀ x : E, ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => (gseq k t).inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) x) atTop
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => (g t).inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) x)))
    (hbound : ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ∀ t ∈ J, ∀ x ∈ g0.metric.ball 0 R, (Dseq k t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ J, ∀ x : E, |(D t).curvatureTensorNorm x| ≤ K := by
  apply curvature_bound_of_tendsto_on_standard_exhaustion g0 D
    (fun k t x => (Dseq k t).curvatureTensorNorm x) _ hbound
  intro t ht x
  exact LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets
    (fun k => Dseq k t) (D t) x (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (hjets t ht x)





theorem curvature_locally_bounded_of_standard_exhaustion
    (g0 : StandardInitialMetric) {lifetime : ℝ}
    (F : RicciFlow 3 E (Ico 0 lifetime))
    (hbound : ∀ T0 : ℝ, 0 ≤ T0 → T0 < lifetime →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
        ∀ t ∈ Icc 0 T0, ∀ x ∈ g0.metric.ball 0 R,
          (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ T0 : ℝ, 0 ≤ T0 → T0 < lifetime →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 T0, ∀ x : E,
        |(F.connection t).curvatureTensorNorm x| ≤ K := by
  intro T0 hT0 hTlife
  obtain ⟨K, hK, hR⟩ := hbound T0 hT0 hTlife
  exact ⟨K, hK, fun t ht => curvature_bound_of_standard_exhaustion g0
    (F.connection t) (fun R hRpos => hR R hRpos t ht)⟩

end PoincareConjecture.M44
