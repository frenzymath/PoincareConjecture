import PoincareConjecture.Proofs.M47.TerminalSourceCountableFlowPatch
import PoincareConjecture.Proofs.M47.TerminalSourceCountableClosedLimit
import PoincareConjecture.Proofs.M47.TerminalGermsMetricRealization
import PoincareConjecture.Proofs.M47.TerminalGermsChartFlow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_chart_flow
    (U : ℕ → Opens E) [∀ i, Nonempty (U i)] (i j : ℕ)
    (M : {k : ℕ // j ≤ k} → Type u)
    [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace E (M a)]
    [∀ a, IsManifold (𝓡 3) ∞ (M a)]
    {tau R : ℝ} (htau : 0 < tau) (hUR : (U i : Set E) ⊆ Metric.ball 0 R)
    (F : ∀ a, RicciFlow 3 (M a) (Icc (-tau) 0))
    (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)
    (f0 : ℕ → E → V) {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (B : ℝ × E → V)
    (hB : ContDiffOn ℝ ∞ B (Icc (-(tau / 4)) 0 ×ˢ (U i : Set E)))
    (hconv : ∀ t ∈ Icc (-(tau / 4)) 0, ∀ x ∈ U i,
      Tendsto (fun k => terminalSourceCountableNegative j M F C f0 (sigma k) (t, x))
        atTop (𝓝 (B (t, x))))
    (hlower : ∀ t ∈ Icc (-(tau / 4)) 0, ∀ x ∈ U i, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in atTop, ∀ v,
        c * ‖v‖ ^ 2 ≤ terminalSourceCountableNegative j M F C f0 (sigma k) (t, x) v v)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ (U i : Set E) →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (terminalSourceCountableNegative j M F C f0 (sigma k)))
        (iteratedFDeriv ℝ m B) atTop K)
    (g0 : CanonicalMetric (fun n => (U n : Set E)) (fun n => (U n).isOpen) i)
    (hterminal :
      letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      ∀ (x : U i) v w, g0.inner x v w = B (0, x) v w) :
    letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∃ G : RicciFlow 3 (U i) (Icc (-(tau / 4)) 0), G.metric 0 = g0 ∧
      ∀ t ∈ Icc (-(tau / 4)) 0, ∀ (x : U i) v w,
        (G.metric t).inner x v w = B (t, x) v w := by
  let source := fun k => terminalSourceCountableSourceIndex j (sigma k)
  let patch := fun k => terminalSourceCountableSourceFlow j M htau F (sigma k)
  let e := fun (k : ℕ) (x : U i) => (C (source k)).chart x.val
  have he (k : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i) x).comp (𝓡 3) _
      ((C (source k)).chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        ((C (source k)).source.symm ▸ hUR x.property))
  let seq := fun (k : ℕ) (z : ℝ × E) => ((patch k).metric z.1).pullbackCoefficients
    (ChartDistance.chartParametrization (fun n => (U n : Set E))
      (fun n => (U n).isOpen) (e k)) z.2
  have hread (k : ℕ) (t : ℝ) : EqOn (fun x => seq k (t, x))
      (((patch k).metric t).pullbackCoefficients (C (source k)).chart) (U i) := by
    exact terminalSourceCountable_pullback_readout U ((patch k).metric t)
      ((patch k).metric t) (he k).contMDiff (C (source k)).chart
      ((C (source k)).smooth.mono hUR) (fun _ _ _ => rfl)
  have heq : ∀ᶠ k in atTop, EqOn (seq k)
      (terminalSourceCountableNegative j M F C f0 (sigma k)) (univ ×ˢ (U i : Set E)) := by
    filter_upwards [terminalSourceCountableSourceFlow_eventually_coefficients
      j M htau F C f0 hsigma] with k hk
    intro z hz
    exact (hread k z.1 hz.2).trans (congrFun hk z)
  have hseqconv (t : ℝ) (ht : t ∈ Icc (-(tau / 4)) 0) (x : E) (hx : x ∈ U i) :
      Tendsto (fun k => seq k (t, x)) atTop (𝓝 (B (t, x))) := by
    apply (hconv t ht x hx).congr'
    exact heq.mono fun k hk => (hk ⟨mem_univ t, hx⟩).symm
  have hseqjet : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ (U i : Set E) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (seq k))
        (iteratedFDeriv ℝ m B) atTop K := by
    intro m K hK hKU
    apply (hjet m K hK hKU).congr
    filter_upwards [heq] with k hk z hz
    have hgerm : seq k =ᶠ[𝓝 z] terminalSourceCountableNegative j M F C f0 (sigma k) := by
      filter_upwards [(isOpen_univ.prod (U i).isOpen).mem_nhds
        (show z ∈ univ ×ˢ (U i : Set E) from ⟨mem_univ _, (hKU hz).2⟩)] with y hy
      exact hk hy
    exact ((hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds).symm
  have heCanonical : letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k) := by
    rw [canonicalDomain_chartedSpace_eq_opens]
    exact he
  let := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  obtain ⟨g, hg, hcoeff, hg0⟩ := terminalGerms_realize_chart_metric
    (fun n => (U n : Set E)) (fun n => (U n).isOpen) i
    (show (0 : ℝ) ∈ Icc (-(tau / 4)) 0 from ⟨by linarith, le_rfl⟩)
    seq B hB (fun k _ _ _ _ _ _ => ((patch k).metric _).symm _ _ _)
    (by
      intro t ht x hx v w
      have hEval : Continuous (fun A : V => A v w) :=
        (continuous_id.clm_apply continuous_const).clm_apply continuous_const
      exact (hEval.tendsto _).comp (hseqconv t ht x hx)) (by
        intro t ht x hx
        obtain ⟨c, hc, hbound⟩ := hlower t ht x hx
        refine ⟨c, hc, ?_⟩
        filter_upwards [hbound, heq] with k hk heqk v
        rw [heqk ⟨mem_univ t, hx⟩]
        exact hk v) g0 hterminal
  obtain ⟨G, hG⟩ := terminalGerms_exists_closed_chart_flow
    (fun n => (U n : Set E)) (fun n => (U n).isOpen)
    (show -(tau / 4) < 0 by linarith) patch i e heCanonical g hg B hcoeff hseqjet
  exact ⟨G, by rw [hG]; exact hg0, by rw [hG]; exact hcoeff⟩

end PoincareConjecture.M47
