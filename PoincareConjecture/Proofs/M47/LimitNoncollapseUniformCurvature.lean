import PoincareConjecture.Proofs.M47.LimitNoncollapseMovingCurvature
import Mathlib.Topology.Sequences










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable {S : GeneralizedBlowupSequence.{u}} {H : ENNReal}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

local instance : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
local instance : SecondCountableTopology G.limit.carrier.carrier := G.limit.carrier.secondCountable




theorem limitNoncollapse_generalized_compact_curvature_lt
    (P : M47Predecessors.{u})
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ blowupBackwardInterval H)
    {Kspace : Set G.limit.sliceCarrier.carrier} (hKspace : IsCompact Kspace)
    {B : ℝ} (hB : ∀ s ∈ Ktime, ∀ x ∈ Kspace,
      (G.limit.flow.connection s).curvatureTensorNorm x < B) :
    ∀ᶠ k : ℕ in atTop,
      Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      Kspace ⊆ G.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ hs : s ∈ Icc (-G.exhaustion.time k) 0, ∀ x ∈ Kspace,
        (S.flow (G.subsequence k)).curvatureNorm ((G.embedding k).pointMap s hs x) /
          S.scale (G.subsequence k) < B := by
  classical
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hKspace
  have hcoverage : ∀ᶠ k in atTop,
      Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧ Kspace ⊆ G.exhaustion.space k := by
    filter_upwards [G.exhaustion.time_cofinal Ktime hKtime hKJ, eventually_ge_atTop j]
      with k htime hjk
    exact ⟨htime, hj.trans (G.exhaustion.space_increasing hjk)⟩
  suffices hb : ∀ᶠ k : ℕ in atTop,
      ∀ s ∈ Ktime, ∀ hs : s ∈ Icc (-G.exhaustion.time k) 0, ∀ x ∈ Kspace,
        (S.flow (G.subsequence k)).curvatureNorm ((G.embedding k).pointMap s hs x) /
          S.scale (G.subsequence k) < B by
    filter_upwards [hcoverage, hb] with k hc hk
    exact ⟨hc.1, hc.2, hk⟩
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ k ≥ N, ∃ s ∈ Ktime,
      ∃ hs : s ∈ Icc (-G.exhaustion.time k) 0, ∃ x ∈ Kspace,
        B ≤ (S.flow (G.subsequence k)).curvatureNorm
          ((G.embedding k).pointMap s hs x) / S.scale (G.subsequence k) := by
    simpa only [eventually_atTop, not_exists, not_forall, Classical.not_imp, not_lt,
      exists_prop] using hnot
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcoverage
  choose k hk s hs hvalid x hx hfail using fun m => hbad (max m N)
  have hindex : Tendsto k atTop atTop := tendsto_atTop_atTop.mpr (fun b =>
    ⟨b, fun m hm => hm.trans ((le_max_left m N).trans (hk m))⟩)
  have hselected (m : ℕ) : Ktime ⊆ Icc (-G.exhaustion.time (k m)) 0 ∧
      Kspace ⊆ G.exhaustion.space (k m) := hN (k m) ((le_max_right m N).trans (hk m))
  obtain ⟨p, hp, f, hf, hconv⟩ := (hKtime.prod hKspace).tendsto_subseq
    (fun m => (show (s m, x m) ∈ Ktime ×ˢ Kspace from ⟨hs m, hx m⟩))
  let c := extChartAt (𝓡 3) p.2
  have hpchart : c p.2 ∈ c.target := c.map_source (mem_extChartAt_source p.2)
  have hz : Tendsto (fun m => (s (f m), c (x (f m)))) atTop (𝓝 (p.1, c p.2)) :=
    (continuousAt_fst.prodMk ((continuousAt_extChartAt (I := 𝓡 3) p.2).comp
      continuousAt_snd)).tendsto.comp hconv
  have hn := limitNoncollapse_tendsto_moving_coordinate_curvature G P p.2 hKtime hKJ
    (hindex.comp hf.tendsto_atTop) (fun m => hs (f m)) hp.1
    (fun m => (hselected (f m)).1 (hs (f m))) hpchart hz
  rw [c.left_inv (mem_extChartAt_source p.2)] at hn
  have hchart := (continuousAt_snd.tendsto.comp hconv).eventually
    (extChartAt_source_mem_nhds (I := 𝓡 3) p.2)
  obtain ⟨m, hm, hcm⟩ := ((hn.eventually (Iio_mem_nhds (hB p.1 hp.1 p.2 hp.2))).and
    hchart).exists
  change (S.flow (G.subsequence (k (f m)))).curvatureNorm
    ((G.embedding (k (f m))).pointMap (s (f m)) _ (c.symm (c (x (f m))))) /
      S.scale (G.subsequence (k (f m))) < B at hm
  change x (f m) ∈ c.source at hcm
  rw [c.left_inv hcm] at hm
  exact (not_lt_of_ge (hfail (f m))) hm

end PoincareConjecture.M47
