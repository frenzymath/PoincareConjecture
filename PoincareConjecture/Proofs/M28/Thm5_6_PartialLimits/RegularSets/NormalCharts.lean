import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_uniform_regular_normal_charts
    (n : ℕ) {K δ r₀ κ : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hr₀ : 0 < r₀) (hκ : 0 < κ) :
    ∃ R ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ R < δ ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M),
      (∀ x ∈ regularComponent g p (2 * δ), D.curvatureTensorNorm x ≤ K) →
      (∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ q ∈ regularComponent g p s,
        (∀ x ∈ g.ball q s, |D.curvatureTensorNorm x| ≤ s⁻¹ ^ 2) →
        ENNReal.ofReal (κ * s ^ n) ≤ g.volumeMeasure (g.ball q s)) →
      ∀ q ∈ regularComponent g p (4 * δ),
        ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
          Φ.source = Metric.ball 0 R ∧ Φ.target = g.ball q R ∧ Φ 0 = q ∧
          (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
            (extChartAt (𝓡 n) q q) (L v) (L w) = inner ℝ v w) ∧
          HasFDerivAt (fun w => extChartAt (𝓡 n) q (Φ w)) L.toContinuousLinearMap 0 ∧
          (∀ w ∈ Metric.ball 0 R,
            g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
          (∀ w ∈ Metric.ball 0 R, g.edist q (Φ w) = ENNReal.ofReal ‖w‖) ∧
          (∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ w,
            (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients Φ x w w ∧
              g.pullbackCoefficients Φ x w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2) ∧
          Φ.target ⊆ regularComponent g p (2 * δ) := by
  have hKone : 0 < K + 1 := by linarith
  let a := min (δ / 4) (min r₀ (K + 1)⁻¹) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ham : a ≤ min (δ / 4) (min r₀ (K + 1)⁻¹) := half_le_self (by positivity)
  have haδ : a ≤ δ / 4 := ham.trans (min_le_left _ _)
  have har₀ : a ≤ r₀ := ham.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haK : a ≤ (K + 1)⁻¹ := ham.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKinv : K + 1 ≤ a⁻¹ := by
    simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hKone) ha).mpr haK
  have hKbound : K ≤ a⁻¹ ^ 2 :=
    (show K ≤ (K + 1) ^ 2 by nlinarith only [hK, sq_nonneg K]).trans
      (pow_le_pow_left₀ hKone.le hKinv 2)
  let v := κ * a ^ n
  have hv : 0 < v := by dsimp [v]; positivity
  let R := RiemannianMetric.localInjectivityRadius n K a v
  have hR : 0 < R := RiemannianMetric.localInjectivityRadius_pos n K ha v
  have hRa : R < a := RiemannianMetric.localInjectivityRadius_lt n K ha v
  obtain ⟨ρ, hρ, hρR, hsmall⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius hR K
  refine ⟨R, ρ, hρ, hρR, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ g D p hcurv hnoncollapse q hq
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcompact : IsCompact (closure (g.ball q (3 * a))) :=
    regularComponent_subset g p (4 * δ) hq (3 * a) (by linarith)
  have hsub : g.ball q (3 * a) ⊆ regularComponent g p (2 * δ) :=
    ball_subset_regularComponent g hq (by positivity) (by linarith)
  have hvolume : ∀ x ∈ g.ball q a,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball x a) := by
    intro x hx
    apply hnoncollapse a ha har₀ x
      (ball_subset_regularComponent g hq ha (by linarith : a + a ≤ 4 * δ) hx)
    intro y hy
    have hyq : y ∈ g.ball q (3 * a) :=
      riemannian_ball_subset_of_margin g ha.le ha.le hx (by linarith) hy
    rw [abs_of_nonneg (show 0 ≤ D.curvatureTensorNorm y from Real.sqrt_nonneg _)]
    exact (hcurv y (hsub hyq)).trans hKbound
  have hqball : q ∈ g.ball q a := by
    change g.edist q q < ENNReal.ofReal a
    rw [show g.edist q q = 0 from Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr ha
  obtain ⟨L, Φ, hsource, htarget, hzero, hL, hderiv, hgeo, hdist, hcoeff⟩ :=
    exists_normal_chart_of_local_noncollapse g D q hn hK ha hv ha
      (show a + 2 * a ≤ 3 * a by linarith) rfl hρR hsmall hcompact
      (fun x hx => hcurv x (hsub hx)) hvolume q hqball
  refine ⟨L, Φ, hsource, htarget, hzero, hL, hderiv, hgeo, hdist, hcoeff, ?_⟩
  rw [htarget]
  exact ball_subset_regularComponent g hq hR (by linarith)

end PoincareConjecture.M28
