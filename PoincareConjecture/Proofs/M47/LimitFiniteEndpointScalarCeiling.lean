import PoincareConjecture.Proofs.M47.LimitFiniteEndpointCapture
import PoincareConjecture.Proofs.M47.TerminalCurvatureActualUniformScalar
import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactBuffers
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceCharts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "seq" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H)) (sigma eta : ℕ → ℕ)

private local instance endpointCeilingTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance endpointCeilingCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance endpointCeilingManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance endpointCeilingT3 : T3Space G.limit.carrier.carrier :=
  G.limit.carrier.t3Space

local notation "X" => G.limit.sliceCarrier.carrier
local notation "n" => (fun k : ℕ => G.subsequence (sigma (eta k)))
local notation "q" => (fun k : ℕ => GeneralizedBlowupSequence.scale seq (n k))
local notation "t" => (fun k : ℕ => baseTime (n k) + -H.toReal / q k)
local notation "gSource" => (fun k : ℕ =>
  rescaledMetric (SurgeryFlowData.metric (F (n k)) (t k)) (q k)
    (GeneralizedBlowupSequence.base_scalar_pos seq (n k)))



theorem limitFinite_endpoint_scalar_ceiling
    {ι : Type v} (gE : RiemannianMetric 3 X) (DE : LeviCivitaData gE)
    {Bendpoint : ℝ} (hnorm : ∀ x, DE.curvatureTensorNorm x ≤ Bendpoint)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((F (n k)).slice (t k)).carrier ∞)
    (hsource : ∀ k, (psi k).source = G.exhaustion.space k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjets : ∀ i m, m ≤ 2 → ∀ C, IsCompact C → C ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gSource k).pullbackCoefficients (psi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (gE.pullbackCoefficients (c i).symm)) atTop C) :
    let K := max 1 (3 * Bendpoint)
    1 ≤ K ∧ ∀ V : Set X, IsCompact V → ∀ᶠ k in atTop,
      V ⊆ (psi k).source ∧ ∀ x ∈ V,
        ((F (n k)).connection (t k)).scalarCurvature (psi k x) ≤ (2 * K) * q k := by
  classical
  let K0 := max 1 (3 * Bendpoint)
  have hK0 : 0 < K0 := zero_lt_one.trans_le (le_max_left _ _)
  have hscalar (x : X) : DE.scalarCurvature x ≤ K0 :=
    (le_abs_self _).trans ((DE.abs_scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      ((mul_le_mul_of_nonneg_left (hnorm x) (by norm_num : (0 : ℝ) ≤ 3)).trans
        (le_max_right _ _)))
  refine ⟨le_max_left _ _, ?_⟩
  intro V hV
  by_cases hVne : V.Nonempty
  · obtain ⟨s, _hsne, index, C, hC, hCtarget, hcover⟩ :=
      terminalCurvature_exists_finite_original_chart_buffers c hV hVne
        (fun x _ => hcoverC x)
    let D : ∀ k, LeviCivitaData (gSource k) := fun k =>
      rescaledMetric_connection ((F (n k)).metric (t k))
        ((F (n k)).connection (t k)) (q k) ((seq).base_scalar_pos (n k))
    have herrors : ∀ᶠ k in atTop, ∀ i : s, ∀ z ∈ C i,
        |(D k).scalarCurvature (psi k ((c (index i)).symm z)) -
          DE.scalarCurvature ((c (index i)).symm z)| < K0 := by
      apply Filter.eventually_all.mpr
      intro i
      have hcharts := terminalCurvature_source_chart_readout
        G.exhaustion.space G.exhaustion.space_open G.exhaustion.space_increasing
        G.exhaustion.space_covers psi hsource (c (index i)) (hC i) (hCtarget i)
      have herr := terminalCurvature_eventually_actual_scalar_error D DE
        (fun k => ((psi k).symm.trans (c (index i))).symm) (c (index i)).symm
        (hC i) (hCtarget i) hcharts.2 (fun m hm => ?_) hK0
      · simpa only [hcharts.1, Function.comp_apply] using herr
      · simpa only [hcharts.1] using hjets (index i) m hm (C i) (hC i) (hCtarget i)
    obtain ⟨j, hj⟩ := hV.elim_directed_cover G.exhaustion.space
      G.exhaustion.space_open
      (by rw [G.exhaustion.space_covers]; exact subset_univ _)
      G.exhaustion.space_increasing.directed_le
    filter_upwards [herrors, eventually_ge_atTop j] with k hk hjk
    refine ⟨?_, ?_⟩
    · rw [hsource k]
      exact hj.trans (G.exhaustion.space_increasing hjk)
    · intro x hx
      obtain ⟨i, hxi, hCx⟩ := hcover x hx
      have herr := hk i (c (index i) x) hCx
      have hinverse : (c (index i)).symm (c (index i) x) = x := (c (index i)).left_inv hxi
      rw [hinverse] at herr
      change |(rescaledMetric_connection _ _ _ _).scalarCurvature (psi k x) -
        DE.scalarCurvature x| < K0 at herr
      rw [rescaledMetric_scalarCurvature] at herr
      have hnormalized : ((F (n k)).connection (t k)).scalarCurvature (psi k x) / q k ≤
          2 * K0 := by
        rw [div_eq_mul_inv, mul_comm]
        linarith [(abs_lt.mp herr).2, hscalar x]
      exact (div_le_iff₀ ((seq).base_scalar_pos (n k))).mp hnormalized
  · have hVempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hVne
    subst V
    exact Eventually.of_forall (fun _ => ⟨empty_subset _, fun _ hx => False.elim hx⟩)



theorem limitFinite_endpoint_scalar_ceiling_on_terminal_ball
    {ι : Type v} (gE : RiemannianMetric 3 X) (DE : LeviCivitaData gE)
    {Bendpoint : ℝ} (hnorm : ∀ x, DE.curvatureTensorNorm x ≤ Bendpoint)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((F (n k)).slice (t k)).carrier ∞)
    (hsource : ∀ k, (psi k).source = G.exhaustion.space k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjets : ∀ i m, m ≤ 2 → ∀ C, IsCompact C → C ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gSource k).pullbackCoefficients (psi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (gE.pullbackCoefficients (c i).symm)) atTop C) :
    let K := max 1 (3 * Bendpoint)
    1 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ j,
      closure ((G.limit.flow.metric 0).ball G.limit.base R) ⊆ G.exhaustion.space j ∧
      ∀ᶠ k in atTop, closure (G.exhaustion.space j) ⊆ (psi k).source ∧
        ∀ x ∈ closure (G.exhaustion.space j),
          ((F (n k)).connection (t k)).scalarCurvature (psi k x) ≤ (2 * K) * q k := by
  have hbound := limitFinite_endpoint_scalar_ceiling F W history baseTime hbaseTime basePoint
    hPositive hDiverges G sigma eta gE DE hnorm psi hsource c hcoverC hjets
  refine ⟨hbound.1, ?_⟩
  intro R _hR
  have hcompact := terminalCommonInterval_compact_ball_closure (G.limit.flow.metric 0)
    (G.limit.complete 0 G.limit.zero_mem) G.limit.base R
  obtain ⟨j, hj⟩ := hcompact.elim_directed_cover G.exhaustion.space
    G.exhaustion.space_open
    (by rw [G.exhaustion.space_covers]; exact subset_univ _)
    G.exhaustion.space_increasing.directed_le
  exact ⟨j, hj, hbound.2 _ (G.exhaustion.space_compactClosure j)⟩

end PoincareConjecture.M47
