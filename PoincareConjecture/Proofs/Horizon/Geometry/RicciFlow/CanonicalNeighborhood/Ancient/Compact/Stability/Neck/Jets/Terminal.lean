import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_normalized_parametrized_jets_at_of_chart_bound
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (q : G.limit.carrier.carrier) {K : Set G.limit.carrier.carrier}
    (hK : IsCompact K) (hKchart : K ⊆ (extChartAt (𝓡 3) q).source)
    {ι : Type*} (f : ι → E → G.limit.carrier.carrier)
    (hf : ∀ i, ∃ U, IsOpen U ∧ (0 : E) ∈ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f i) U)
    (hmap : ∀ i, f i 0 ∈ K)
    (m : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hfj : ∀ i j, 1 ≤ j → j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j ((extChartAt (𝓡 3) q) ∘ f i) 0‖ ≤ C)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ (i : ι) (j : ℕ), j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => s k •
        ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
          (fun x => ((e k).toFun (0, f i x)).2) y -
        s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (f i) y) 0‖ ≤ η := by
  let c := extChartAt (𝓡 3) q
  let α := fun i => c ∘ f i
  let L := c '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    ((continuousOn_extChartAt q).mono hKchart)
  have hLc : L ⊆ c.target := image_subset_iff.mpr fun x hx => c.map_source (hKchart hx)
  have hα (i : ι) : ContDiffAt ℝ ∞ (α i) 0 := by
    obtain ⟨U, hU, h0, hfi⟩ := hf i
    exact contMDiffAt_iff_contDiffAt.mp
      (((contMDiffOn_extChartAt (n := ∞) (x := q)).contMDiffAt
        (by simpa only [extChartAt_source] using
          (isOpen_extChartAt_source (I := 𝓡 3) q).mem_nhds (hKchart (hmap i)))).comp 0
          (hfi.contMDiffAt (hU.mem_nhds h0)))
  let B := fun k y => s k •
    ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
      (fun x => ((e k).toFun (0, c.symm x)).2) y -
    s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients c.symm y
  obtain ⟨hlocal, hjet⟩ := hconv.smooth_zero_convergence_terminal_normalized_parametrized
    hfixed (ContinuousLinearEquiv.refl ℝ E) (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm (n := ∞) q) hs
  have hb := TerminalNeck.eventually_small_bilinearPullback_jets_of_compact_convergence
    (B := B) (f := α) (fun _ : ι => (0 : E)) hL hLc hα
    (fun i => mem_image_of_mem c (hmap i)) hlocal m hC hfj
    (fun j _ => hjet j L hL hLc) hη
  obtain ⟨k₀, hk₀⟩ := G.exists_exhaustion_superset hK
  filter_upwards [hb, eventually_ge_atTop k₀] with k hkb hkk i j hj
  obtain ⟨U, hU, h0, hfi⟩ := hf i
  let V := U ∩ (f i) ⁻¹' (c.source ∩ G.exhaustion k)
  have hV : IsOpen V := hfi.continuousOn.isOpen_inter_preimage hU
    ((isOpen_extChartAt_source (I := 𝓡 3) q).inter (G.exhaustion_open k))
  have h0V : (0 : E) ∈ V := ⟨h0, hKchart (hmap i),
    G.exhaustion_monotone hkk (hk₀ (hmap i))⟩
  have hαV : ContDiffOn ℝ ∞ (α i) V := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (contMDiffOn_extChartAt (n := ∞) (x := q)).comp
      (hfi.mono inter_subset_left)
      (fun y hx => by
        change f i y ∈ (chartAt E q).source
        simpa only [c, extChartAt_source] using hx.2.1)
  have heq : (fun y => (B k (α i y)).bilinearComp
      (fderiv ℝ (α i) y) (fderiv ℝ (α i) y)) =ᶠ[𝓝 (0 : E)]
      (fun y => s k •
        ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
          (fun x => ((e k).toFun (0, f i x)).2) y -
        s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (f i) y) := by
    filter_upwards [hV.mem_nhds h0V] with y hy
    have hct : α i y ∈ c.target := c.map_source hy.2.1
    have hc : c.symm (α i y) = f i y := c.left_inv hy.2.1
    have hcs := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hct)
    have hes := ((e k).contMDiffOn_terminalSpatialMap (t := 0) le_rfl).contMDiffAt
      ((G.exhaustion_open k).mem_nhds hy.2.2)
    let ψ := fun x => ((e k).toFun (0, c.symm x)).2
    have hψ : MDifferentiableAt (𝓡 3) (𝓡 3) ψ (α i y) := by
      rw [← hc] at hes
      exact (hes.comp _ hcs).mdifferentiableAt (by simp)
    have hcomp : ψ ∘ α i =ᶠ[𝓝 y] (fun x => ((e k).toFun (0, f i x)).2) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      dsimp only [ψ, α, Function.comp_apply]
      rw [c.left_inv hz.2.1]
    have hcomp₀ : c.symm ∘ α i =ᶠ[𝓝 y] f i := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact c.left_inv hz.2.1
    have hdiff := (hαV.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
    have hsource := ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients_comp_of_eventuallyEq
      hψ hdiff hcomp
    have hlimit := (G.limit.flow.flow.metric 0).parametrizedCoefficients_comp_of_eventuallyEq
      (hcs.mdifferentiableAt (by simp)) hdiff hcomp₀
    ext v w
    exact congrArg₂ (fun a b : ℝ => s k * a - s₀ * b)
      (congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hsource)
      (congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hlimit)
  rw [← (heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact hkb i j hj

end M23TerminalMetricConvergence
end PoincareConjecture
