import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.CompactComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_terminalFlow_pairwise_metric_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ r ∈ Ico s T, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 3) x,
        ((H.terminalFlow P04).metric t).inner x v v ≤
          4 * ((H.terminalFlow P04).metric r).inner x v v := by
  obtain ⟨s, K, hsref, hsT, hK, hmetric⟩ :=
    H.exists_compact_terminal_metric_exponential_comparison P04 hA
  have hexp : Tendsto (fun t : ℝ => Real.exp (6 * K * (T - t))) (𝓝[<] T) (𝓝 1) := by
    have hd : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝 (T - T)) :=
      tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa only [Function.comp_def, sub_self, mul_zero, Real.exp_zero] using
      (Real.continuous_exp.tendsto (6 * K * (T - T))).comp (hd.const_mul (6 * K))
  obtain ⟨a, haT, hsmall⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (hexp.eventually_lt_const (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨b, hb, hbT⟩ := exists_between (max_lt hsT haT)
  have hbs : s < b := (le_max_left _ _).trans_lt hb
  have hba : a < b := (le_max_right _ _).trans_lt hb
  refine ⟨b, hsref.trans hbs, hbT, ?_⟩
  intro t ht r hr x hx v
  have ht' : t ∈ Ico s T := ⟨hbs.le.trans ht.1, ht.2⟩
  have hr' : r ∈ Ico s T := ⟨hbs.le.trans hr.1, hr.2⟩
  have hEt : Real.exp (6 * K * (T - t)) ≤ 2 :=
    le_of_lt (hsmall ⟨hba.trans_le ht.1, ht.2⟩)
  have hEr : Real.exp (6 * K * (T - r)) ≤ 2 :=
    le_of_lt (hsmall ⟨hba.trans_le hr.1, hr.2⟩)
  have hn (g : RiemannianMetric 3 (H.regularRegion P04)) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hl := (hmetric t ht' x hx v).2.trans
    (mul_le_mul_of_nonneg_right hEt (hn (H.terminalMetric P04)))
  have hu := (hmetric r hr' x hx v).1.trans
    (mul_le_mul_of_nonneg_right hEr (hn ((H.terminalFlow P04).metric r)))
  linarith

end PoincareConjecture.SingularTimeAssumptions
