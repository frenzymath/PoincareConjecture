import PoincareConjecture.Proofs.M47.LimitNoncollapseIncludedJets
import Mathlib.Topology.UniformSpace.UniformApproximation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace E C.limit.carrier.carrier := C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold



theorem limitNoncollapse_limit_spatialJet_continuousOn
    (q : C.limit.sliceCarrier.carrier) (r : ℕ) (a b : Fin 3) :
    ContinuousOn (fun z : ℝ × E => iteratedFDeriv ℝ r
      (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
        (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2)
      (blowupMetricChartDomain C.limit q) := by
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex C.limit.flow.interval.convex
    (C.limit.flow.interval.convex.nontrivial_iff_nonempty_interior.mp C.limit.flow.nontrivial)
  let R := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℝ)
    (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)
  have hcont := (C.limit.flow.contDiffOn_chartMetric q a b).continuousOn_iteratedFDerivWithin
    (show (r : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    (hJ.prod (isOpen_extChartAt_target q).uniqueDiffOn)
  apply (R.continuous.comp_continuousOn hcont).congr
  intro z hz
  exact iteratedFDeriv_prod_slice_eq_within (C.limit.flow.contDiffOn_chartMetric q a b)
    hJ (isOpen_extChartAt_target q) hz.1 hz.2 (WithTop.coe_le_coe.mpr le_top)




theorem limitNoncollapse_tendsto_moving_spatial_jets
    (P : M47Predecessors.{u}) (q : C.limit.sliceCarrier.carrier)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    {index : ℕ → ℕ} (hindex : Tendsto index atTop atTop)
    {z : ℕ → ℝ × E} {p : ℝ × E}
    (htime : ∀ k, (z k).1 ∈ Ktime) (hp : p.1 ∈ Ktime)
    (hchart : p.2 ∈ (extChartAt (𝓡 3) q).target)
    (hz : Tendsto z atTop (𝓝 p)) (r : ℕ) (a b : Fin 3) :
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => blowupPullbackCoefficient (C.embedding (index k)) q a b ((z k).1, y))
        (z k).2) atTop
      (𝓝 (iteratedFDeriv ℝ r
        (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (p.1, y)) p.2)) := by
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex C.limit.flow.interval.convex
    (C.limit.flow.interval.convex.nontrivial_iff_nonempty_interior.mp C.limit.flow.nontrivial)
  obtain ⟨H, hH, hpH, hHt⟩ := exists_compact_subset
    (isOpen_extChartAt_target (I := 𝓡 3) q) hchart
  have hzH : ∀ᶠ k in atTop, (z k).2 ∈ H :=
    (continuousAt_snd.tendsto.comp hz).eventually (mem_interior_iff_mem_nhds.mp hpH)
  have hunif : TendstoUniformlyOn
      (fun k (w : ℝ × E) => iteratedFDeriv ℝ r
        (fun y => blowupPullbackCoefficient (C.embedding (index k)) q a b (w.1, y)) w.2)
      (fun w : ℝ × E => iteratedFDeriv ℝ r
        (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v v' => (C.limit.flow.metric t).inner x v v') a b (w.1, y)) w.2)
      atTop (Ktime ×ˢ H) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    filter_upwards [hindex.eventually
      (limitNoncollapse_generalized_compact_spatial_jets P C hJ q r hKtime hKJ hH hHt
        hepsilon)] with k hk w hw
    simpa only [dist_eq_norm, norm_sub_rev] using hk.2.2 w.1 hw.1 w.2 hw.2 a b
  have hwithin : Tendsto z atTop (𝓝[Ktime ×ˢ H] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hzH.mono (fun k hk => ⟨htime k, hk⟩)⟩
  exact hunif.tendsto_comp
    ((limitNoncollapse_limit_spatialJet_continuousOn C q r a b p ⟨hKJ hp, hchart⟩).mono
      (fun w hw => ⟨hKJ hw.1, hHt hw.2⟩)) hwithin

end PoincareConjecture.M47
