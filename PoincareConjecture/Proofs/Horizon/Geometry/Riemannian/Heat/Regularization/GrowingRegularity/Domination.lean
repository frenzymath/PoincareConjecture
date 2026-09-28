import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Harnack











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}



theorem exists_dirichletExhaustionKernel_later_row_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (hΩ : ∀ q, IsOpen (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    {H : ℕ → ℝ → M → M → ℝ}
    (hH : ∀ q, Dirichlet.IsDirichletHeatKernel D (Ω q) (H q))
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun q => H q t x y))
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, ∀ x,
      (g.edist O x).toReal ≤ R → ∀ y,
      dirichletExhaustionKernel H t x y ≤
        C * dirichletExhaustionKernel H (b + 1) O y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA, harnack⟩ :=
    D.exists_dirichletExhaustionKernel_harnack_on_intrinsic_ball hn hc hk hRic O hR
  let C : ℝ := Real.exp (2 * (n : ℝ) * Real.log ((b + 1) / a) +
    A * (b + 1) + R ^ 2 / 2)
  refine ⟨C, Real.exp_pos _, ?_⟩
  intro t ht x hx y
  have ht0 : 0 < t := ha.trans_le ht.1
  have hb0 : 0 < b + 1 := by linarith
  have htb : t < b + 1 := by linarith [ht.2]
  have hself : (g.edist O O).toReal = 0 := by
    have heq : g.edist O O = 0 := by
      simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    rw [heq, ENNReal.toReal_zero]
  have hdist : (g.edist x O).toReal ≤ R := by
    have heq : g.edist x O = g.edist O x := Manifold.riemannianEDist_comm
    simpa only [heq] using hx
  have hh := harnack Ω hΩ hΩmono hcover H hH hmono
    t (b + 1) ht0 htb x O hx (by rw [hself]; linarith) y
  have hnonneg : 0 ≤ dirichletExhaustionKernel H (b + 1) O y := by
    apply le_ciSup_of_le (D.bddAbove_dirichletHeatKernel_exhaustion
      hn hc hk hRic hΩ hΩmono hcover hH hmono hb0 O y) 0
    exact (hH 0).nonneg (b + 1) hb0 O y
  have hlog : Real.log ((b + 1) / t) ≤ Real.log ((b + 1) / a) :=
    Real.log_le_log (div_pos hb0 ht0)
      (div_le_div_of_nonneg_left hb0.le ha ht.1)
  have hsquare : (g.edist x O).toReal ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg hdist 2
  have hquot : (g.edist x O).toReal ^ 2 / (2 * (b + 1 - t)) ≤ R ^ 2 / 2 := by
    apply (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0 : ℝ) < 2)
      (by linarith [ht.2])).trans
    exact div_le_div_of_nonneg_right hsquare (by norm_num)
  have hexp : Real.exp (2 * (n : ℝ) * Real.log ((b + 1) / t) +
      A * (b + 1 - t) + (g.edist x O).toReal ^ 2 / (2 * (b + 1 - t))) ≤ C := by
    apply Real.exp_le_exp.mpr
    have hfirst := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 2 * (n : ℝ) by positivity)
    have hsecond := mul_le_mul_of_nonneg_left
      (show b + 1 - t ≤ b + 1 by linarith) hA.le
    exact add_le_add (add_le_add hfirst hsecond) hquot
  exact hh.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hexp hnonneg)

end PoincareConjecture.LeviCivitaData
