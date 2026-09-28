import PoincareConjecture.Proofs.M47.TerminalCommonIntervalActualIsometry
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalM30CoefficientJets
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSmoothAssembly
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.ChartTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace

private noncomputable def m30TerminalDiffeomorph (n : ℕ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier ∞ where
  toPartialEquiv := (terminalCommonInterval_m30TerminalMap G n).toPartialEquiv
  open_source := (terminalCommonInterval_m30TerminalMap G n).open_source
  open_target := (terminalCommonInterval_m30TerminalMap G n).open_target
  contMDiffOn_toFun := (terminalCommonInterval_m30_terminal_source G n).2.1
  contMDiffOn_invFun := (terminalCommonInterval_m30_terminal_source G n).2.2

theorem terminalCommonInterval_actual_terminal_identification
    (P : M47Predecessors.{u})
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [PreconnectedSpace M]
    (g : RiemannianMetric 3 M) (hg : MetricComplete g) (p : M)
    (e : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) M
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier ∞)
    (hbase : ∀ n, e n p = (V.base (G.subsequence n)).2)
    (hE : terminalCommonInterval_compactTangentControl g
      (fun n => M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
      (fun n => (e n).toOpenPartialHomeomorph))
    (a : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (ha : ∀ x : M, ∃ i, x ∈ (a i).source)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (a i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m
        (RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric
          ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
          (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
          (e n ∘ (a i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (a i).symm)) atTop K) :
    letI := g.toMetricSpace
    letI : MetricSpace G.limit.carrier.carrier := (G.limit.flow.metric 0).toMetricSpace
    let T : ℕ → OpenPartialHomeomorph M G.limit.carrier.carrier :=
      fun n => (e n).toOpenPartialHomeomorph.trans
        (terminalCommonInterval_m30TerminalMap G n).symm
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ I : Diffeomorph (𝓡 3) (𝓡 3) M G.limit.carrier.carrier ∞,
        I p = G.limit.base ∧
        (∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
          g.inner x v w = (G.limit.flow.metric 0).inner (I x)
            (mfderiv (𝓡 3) (𝓡 3) I x v) (mfderiv (𝓡 3) (𝓡 3) I x w)) ∧
        (∀ j : ℕ, TendstoUniformlyOn (fun n => T (rho n)) I atTop
          (Metric.closedBall p (j + 1))) ∧
        ∀ j : ℕ, TendstoUniformlyOn (fun n => (T (rho n)).symm) I.symm atTop
          (Metric.closedBall G.limit.base (j + 1)) := by
  let k := G.limit.flow.metric 0
  let := g.toMetricSpace
  let : MetricSpace G.limit.carrier.carrier := k.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier :=
    k.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  let eO := fun n => (e n).toOpenPartialHomeomorph
  let f := m30TerminalDiffeomorph G
  let h (n : ℕ) : RiemannianMetric 3
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
    M13.scaleSmoothMetric ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
      (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))
  have he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (eO n) (eO n).source :=
    fun n => (e n).contMDiffOn_toFun.of_le (by simp)
  have hei : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (eO n).symm (eO n).target :=
    fun n => (e n).contMDiffOn_invFun.of_le (by simp)
  obtain ⟨rho, hrho, d, hbased, hforward, hreverse⟩ :=
    terminalCommonInterval_actual_terminal_isometry G g hg p eO he hei hbase hE
  have hsource (K : Set M) (hK : IsCompact K) :
      ∀ᶠ n in atTop, K ⊆ ((e (rho n)).trans (f (rho n)).symm).source := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
    have hA : 0 < max 1 R := zero_lt_one.trans_le (le_max_left _ _)
    have htail := terminalCommonInterval_actual_cross_control G g hg p eO he hei
      hbase hE hA (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [hrho.tendsto_atTop.eventually htail] with n hn x hx
    apply hn.1
    rw [← g.toMetricSpace_closedBall p hA.le]
    exact Metric.closedBall_subset_closedBall (le_max_right _ _) (hR hx)
  have hsourceF (K : Set G.limit.carrier.carrier) (hK : IsCompact K) :
      ∀ᶠ n in atTop, K ⊆ (f (rho n)).source := by
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
    filter_upwards [hrho.tendsto_atTop.eventually (eventually_ge_atTop j)] with n hn
    change K ⊆ (terminalCommonInterval_m30TerminalMap G (rho n)).source
    rw [(terminalCommonInterval_m30_terminal_source G (rho n)).1]
    exact hj.trans (G.exhaustion.space_increasing hn)
  have hconv (K : Set M) (hK : IsCompact K) : TendstoUniformlyOn
      (fun n => (e (rho n)).trans (f (rho n)).symm) d.toHomeomorph atTop K :=
    terminalCommonInterval_uniform_on_compacts_of_balls p hforward hK
  obtain ⟨q, hq⟩ := G.limit.carrier.exists_countable_chart_cover
  let b := fun i => limitCanonicalNativeChart (q i)
  have hjetA (i m : ℕ) (K : Set E) (hK : IsCompact K) (hKa : K ⊆ (a i).target) :
      TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ m ((h (rho n)).pullbackCoefficients
          (e (rho n) ∘ (a i).symm)))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients (a i).symm)) atTop K :=
    fun V hV => hrho.tendsto_atTop.eventually (hjet i m K hK hKa V hV)
  have hjetB (i m : ℕ) (K : Set E) (hK : IsCompact K) (hKb : K ⊆ (b i).target) :
      TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ m ((h (rho n)).pullbackCoefficients
          (f (rho n) ∘ (b i).symm)))
        (iteratedFDeriv ℝ m (k.pullbackCoefficients (b i).symm)) atTop K :=
    fun V hV => hrho.tendsto_atTop.eventually
      (terminalCommonInterval_m30_terminal_coefficient_jets G P (q i) m hK hKb V hV)
  obtain ⟨I, hI, hIinv, hinner, _sigma, _hsigma, _hjets⟩ :=
    terminalCommonInterval_diffeomorph_of_actual_jets g k (fun n => h (rho n))
      (fun n => e (rho n)) (fun n => f (rho n)) d.toHomeomorph hsource hsourceF hconv
      a b ha hq hjetA hjetB
  refine ⟨rho, hrho, I, ?_, hinner, ?_, ?_⟩
  · exact (congrFun hI p).trans hbased
  · simpa only [hI, IsometryEquiv.coe_toHomeomorph] using hforward
  · simpa only [hIinv, IsometryEquiv.coe_toHomeomorph_symm] using hreverse

end PoincareConjecture.M47
