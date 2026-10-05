import PoincareLib.Geometry.RicciFlow.Local.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Energy.Regularity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The union of ordinary restart intervals

Uniqueness identifies every compact-time solution with the same initial metric
on overlaps. Choosing those solutions pointwise therefore gives one smooth
Ricci flow up to the supremum of their existence times. This is the ordinary
restart construction used in Morgan--Tian, Definition 15.8, pp. 361-362,
from Theorem 3.11, p. 39, and Proposition 4.12, p. 68.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.Surgery.OrdinaryRestart

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A positive finite ordinary interval starting at the specified metric. -/
structure Solution (g₀ : RiemannianMetric n M) where
  time : ℝ
  time_pos : 0 < time
  flow : RicciFlow n M (Ico 0 time)
  initial : flow.metric 0 = g₀

variable {g₀ : RiemannianMetric n M}

/-- Uniqueness makes the finite restart intervals compatible. -/
theorem Solution.metric_eq (hunique : RicciFlowUniqueness n M)
    (A B : Solution g₀) {t : ℝ} (htA : t ∈ Ico 0 A.time)
    (htB : t ∈ Ico 0 B.time) : A.flow.metric t = B.flow.metric t := by
  exact hunique _ _ A.flow B.flow ⟨⟨le_rfl, A.time_pos⟩, fun _ h => h.1⟩
    ⟨⟨le_rfl, B.time_pos⟩, fun _ h => h.1⟩ (A.initial.trans B.initial.symm)
    ⟨htA, htB⟩

/-- The maximal ordinary lifetime, allowing an immortal restart. -/
noncomputable def lifetime (g₀ : RiemannianMetric n M) : ℝ≥0∞ :=
  ⨆ A : Solution g₀, ENNReal.ofReal A.time

/-- Times strictly below the supremum belong to a finite restart interval. -/
theorem exists_solution_at {t : ℝ} (ht : 0 ≤ t)
    (h : ENNReal.ofReal t < lifetime g₀) :
    ∃ A : Solution g₀, t < A.time := by
  obtain ⟨A, hA⟩ := (lt_iSup_iff).mp h
  exact ⟨A, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp hA⟩

/-- Every finite restart interval lies in the maximal interval. -/
theorem solution_time_lt (A : Solution g₀) {t : ℝ} (ht : t < A.time) :
    ENNReal.ofReal t < lifetime g₀ := by
  exact ((ENNReal.ofReal_lt_ofReal_iff A.time_pos).mpr ht).trans_le
    (le_iSup (fun B : Solution g₀ => ENNReal.ofReal B.time) A)

/-- A local restart guarantees a positive maximal lifetime. -/
theorem lifetime_pos (A : Solution g₀) : 0 < lifetime g₀ := by
  simpa only [ENNReal.ofReal_zero] using solution_time_lt A A.time_pos

/-- Choose a finite solution at each time; outside the maximal interval use the seed. -/
noncomputable def solutionAt (A : Solution g₀) (t : ℝ) : Solution g₀ :=
  if h : 0 ≤ t ∧ ENNReal.ofReal t < lifetime g₀ then
    (exists_solution_at h.1 h.2).choose else A

/-- The selected solution exists beyond the selected time. -/
theorem solutionAt_time (A : Solution g₀) {t : ℝ}
    (ht : 0 ≤ t ∧ ENNReal.ofReal t < lifetime g₀) :
    t < (solutionAt A t).time := by
  simp only [solutionAt, dif_pos ht]
  exact (exists_solution_at ht.1 ht.2).choose_spec

/-- The selected metric agrees with each solution throughout its interval. -/
theorem selected_metric_eq (hunique : RicciFlowUniqueness n M)
    (A B : Solution g₀) {t : ℝ} (ht : t ∈ Ico 0 B.time) :
    (solutionAt A t).flow.metric t = B.flow.metric t := by
  exact (solutionAt A t).metric_eq hunique B
    ⟨ht.1, solutionAt_time A ⟨ht.1, solution_time_lt B ht.2⟩⟩ ht

/-- A finite solution interval is a relative neighborhood at each of its times. -/
theorem solution_interval_mem (B : Solution g₀) {t : ℝ} (ht : t ∈ Ico 0 B.time) :
    Ico 0 B.time ∈ 𝓝[{s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < lifetime g₀}] t := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds ht.2)] with s hs hst
  exact ⟨hs.1, hst⟩

/-- Gluing by uniqueness constructs the ordinary flow on the entire maximal interval. -/
noncomputable def maximalFlow (hunique : RicciFlowUniqueness n M)
    (A : Solution g₀) :
    RicciFlow n M {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < lifetime g₀} where
  metric t := (solutionAt A t).flow.metric t
  connection t := (solutionAt A t).flow.connection t
  interval := ⟨by
    intro a ha b hb t ht
    exact ⟨ha.1.trans ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hb.2⟩⟩
  nontrivial := by
    refine ⟨0, ⟨le_rfl, ?_⟩, A.time / 2, ⟨by linarith [A.time_pos], ?_⟩, ?_⟩
    · simpa only [ENNReal.ofReal_zero] using lifetime_pos A
    · exact solution_time_lt A (by linarith [A.time_pos])
    · linarith [A.time_pos]
  smooth := by
    intro p hp
    let B := solutionAt A p.1
    have ht : p.1 ∈ Ico 0 B.time := ⟨hp.1.1, solutionAt_time A hp.1⟩
    have hneigh : Ico 0 B.time ×ˢ (univ : Set M) ∈
        𝓝[({t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < lifetime g₀} ×ˢ univ)] p := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          ((isOpen_Iio.preimage continuous_fst).mem_nhds ht.2)] with q hq hqt
      exact ⟨⟨hq.1.1, hqt⟩, mem_univ _⟩
    apply ContMDiffWithinAt.congr_of_eventuallyEq_of_mem
      ((B.flow.smooth p ⟨ht, mem_univ _⟩).mono_of_mem_nhdsWithin hneigh) _ hp
    filter_upwards [hneigh] with q hq
    rw [selected_metric_eq hunique A B hq.1]
  equation := by
    intro t ht x v w
    let B := solutionAt A t
    have htB : t ∈ Ico 0 B.time := ⟨ht.1, solutionAt_time A ht⟩
    apply ((B.flow.equation t htB x v w).mono_of_mem_nhdsWithin
      (solution_interval_mem B htB)).congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [solution_interval_mem B htB] with s hs
    rw [selected_metric_eq hunique A B hs]

/-- The union solution starts at exactly the prescribed metric. -/
theorem maximalFlow_initial (hunique : RicciFlowUniqueness n M) (A : Solution g₀) :
    (maximalFlow hunique A).metric 0 = g₀ :=
  (solutionAt A 0).initial

/-- Each finite solution contributes its full lifetime to the union. -/
theorem time_le_lifetime (A : Solution g₀) : ENNReal.ofReal A.time ≤ lifetime g₀ :=
  le_iSup (fun B : Solution g₀ => ENNReal.ofReal B.time) A

/-- At a finite lifetime, the maximal domain has its usual half-open form. -/
theorem finite_domain (hfinite : lifetime g₀ ≠ ⊤) :
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < lifetime g₀} =
      Ico 0 (lifetime g₀).toReal := by
  ext t
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp he⟩
  · rintro ⟨ht, he⟩
    exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mpr he⟩

/-- The finite maximal solution retains the chosen metric and connection families. -/
noncomputable def finiteFlow (hunique : RicciFlowUniqueness n M)
    (A : Solution g₀) (hfinite : lifetime g₀ ≠ ⊤) :
    RicciFlow n M (Ico 0 (lifetime g₀).toReal) where
  metric := (maximalFlow hunique A).metric
  connection := (maximalFlow hunique A).connection
  interval := ordConnected_Ico
  nontrivial := by
    rw [← finite_domain hfinite]
    exact (maximalFlow hunique A).nontrivial
  smooth := by
    rw [← finite_domain hfinite]
    exact (maximalFlow hunique A).smooth
  equation := by
    rw [← finite_domain hfinite]
    exact (maximalFlow hunique A).equation

/-- A finite maximal endpoint cannot have a uniform full-curvature bound. -/
theorem finite_curvature_unbounded (hlocal : RicciFlowLocalTheory n M)
    (A : Solution g₀) (hfinite : lifetime g₀ ≠ ⊤) (C : ℝ) :
    ∃ t ∈ Ico 0 (lifetime g₀).toReal, ∃ x : M,
      C < ((finiteFlow hlocal.2.1 A hfinite).connection t).curvatureTensorNorm x := by
  by_contra h
  push Not at h
  have hpos : 0 < (lifetime g₀).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lifetime_pos A)) hfinite
  obtain ⟨b, hb, F, hF⟩ :=
    hlocal.2.2 _ hpos (finiteFlow hlocal.2.1 A hfinite) ⟨C, h⟩
  let B : Solution g₀ := ⟨b, hpos.trans hb, F,
    (hF ⟨le_rfl, hpos⟩).symm.trans (maximalFlow_initial hlocal.2.1 A)⟩
  have hle := time_le_lifetime B
  have hlt : lifetime g₀ < ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff (hpos.trans hb)).mpr hb
  exact (not_lt_of_ge hle) hlt

/-- An empty ordinary carrier has infinite lifetime. -/
theorem lifetime_eq_top_of_isEmpty [IsEmpty M]
    (hlocal : RicciFlowLocalTheory n M) (A : Solution g₀) : lifetime g₀ = ⊤ := by
  by_contra hfinite
  obtain ⟨_, _, x, _⟩ := finite_curvature_unbounded hlocal A hfinite 0
  exact isEmptyElim x

/-- The local existence service supplies a seed for the maximal union. -/
theorem nonempty_solution (hlocal : RicciFlowLocalTheory n M)
    (g₀ : RiemannianMetric n M) : Nonempty (Solution g₀) := by
  obtain ⟨b, hb, F, hF⟩ := hlocal.1 g₀
  exact ⟨⟨b, hb, F, hF⟩⟩

/-- Compact earlier strips have a uniform full-curvature bound. -/
theorem curvature_bound_on_compact [CompactSpace M] {J K : Set ℝ}
    (F : RicciFlow n M J) (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ C : ℝ, ∀ t ∈ K, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ C := by
  have hE : ContinuousOn
      (fun p : ℝ × M => ((F.connection p.1).curvatureTensorNorm p.2) ^ 2)
      (J ×ˢ univ) := by
    simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using
      (RicciFlowAnalysis.contMDiffOn_flow_curvatureDerivativeEnergy F 0).continuousOn
  have hN : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).curvatureTensorNorm p.2)
      (K ×ˢ univ) := by
    apply (hE.mono (prod_mono hKJ (subset_refl _))).sqrt.congr
    intro p _
    exact (Real.sqrt_sq (show 0 ≤ (F.connection p.1).curvatureTensorNorm p.2 from
      Real.sqrt_nonneg _)).symm
  obtain ⟨C, hC⟩ :=
    (hK.prod (isCompact_univ : IsCompact (univ : Set M))).bddAbove_image hN
  exact ⟨C, fun t ht x => hC ⟨(t, x), ⟨ht, mem_univ _⟩, rfl⟩⟩

/-- Full curvature is unbounded in every tail of a finite maximal restart. -/
theorem finite_curvature_unbounded_tail [CompactSpace M]
    (hlocal : RicciFlowLocalTheory n M) (A : Solution g₀)
    (hfinite : lifetime g₀ ≠ ⊤) (C s : ℝ) (hs : s < (lifetime g₀).toReal) :
    ∃ t ∈ Ioo (max 0 s) (lifetime g₀).toReal, ∃ x : M,
      C < ((maximalFlow hlocal.2.1 A).connection t).curvatureTensorNorm x := by
  have hpos : 0 < (lifetime g₀).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lifetime_pos A)) hfinite
  have hmax : max 0 s < (lifetime g₀).toReal := max_lt hpos hs
  obtain ⟨K, hK⟩ := curvature_bound_on_compact (finiteFlow hlocal.2.1 A hfinite)
    (K := Icc 0 (max 0 s)) isCompact_Icc
    (fun _ ht => ⟨ht.1, ht.2.trans_lt hmax⟩)
  obtain ⟨t, ht, x, hx⟩ := finite_curvature_unbounded hlocal A hfinite (max C K)
  refine ⟨t, ⟨?_, ht.2⟩, x, (le_max_left C K).trans_lt hx⟩
  by_contra h
  exact (not_lt_of_ge (hK t ⟨ht.1, le_of_not_gt h⟩ x)) ((le_max_right C K).trans_lt hx)

/-- Construct a maximal ordinary restart from the local-flow service. -/
theorem exists_maximal_flow [CompactSpace M] (P : RicciFlowLocalTheory n M)
    (g₀ : RiemannianMetric n M) :
    ∃ b : ℝ≥0∞, 0 < b ∧
      ∃ F : RicciFlow n M {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < b},
        F.metric 0 = g₀ ∧
        (∀ c : ℝ, 0 < c → ∀ G : RicciFlow n M (Ico 0 c),
          G.metric 0 = g₀ → ENNReal.ofReal c ≤ b) ∧
        (b ≠ ⊤ → ∀ C s : ℝ, s < b.toReal →
          ∃ t ∈ Ioo (max 0 s) b.toReal, ∃ x : M,
            C < (F.connection t).curvatureTensorNorm x) := by
  obtain ⟨A⟩ := nonempty_solution P g₀
  refine ⟨lifetime g₀, lifetime_pos A, maximalFlow P.2.1 A,
    maximalFlow_initial P.2.1 A, ?_, finite_curvature_unbounded_tail P A⟩
  intro c hc G hG
  exact time_le_lifetime ⟨c, hc, G, hG⟩

end PoincareMT.Surgery.OrdinaryRestart
