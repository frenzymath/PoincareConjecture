import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control









set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow



theorem eventually_ancientRescaleAt_annular_curvature_lt_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ s ≤ 0, ∀ x : M,
      b ≤ (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist p x).toReal →
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).connection s).curvatureTensorNorm x < ε := by
  let C : ℝ := ε * b ^ 2 / ((n : ℝ) ^ 2 + 1)
  have hCpos : 0 < C := by dsimp [C]; positivity
  obtain ⟨L, hdecay⟩ := hzero C hCpos
  have hsmall : Tendsto (fun i => Real.sqrt (Q i) * L) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hQzero).mul_const L
  have hconstant : (n : ℝ) ^ 2 * (C / b ^ 2) < ε := by
    have hdenom : 0 < (n : ℝ) ^ 2 + 1 := by positivity
    have hid : (n : ℝ) ^ 2 * (C / b ^ 2) =
        (n : ℝ) ^ 2 * ε / ((n : ℝ) ^ 2 + 1) := by
      dsimp [C]
      field_simp
    rw [hid]
    apply (div_lt_iff₀ hdenom).mpr
    nlinarith
  filter_upwards [hsmall.eventually_lt_const hb] with i hi
  intro s hs x hx
  exact (F.ancientRescaleAt_curvatureTensorNorm_le_of_quadratic_decay hC hcomplete
    hoperator hK hbound (Q i) (hQ i) t₀ ht₀ p hb hdecay hi.le s hs x hx).trans_lt hconstant

end PoincareConjecture.RicciFlow
