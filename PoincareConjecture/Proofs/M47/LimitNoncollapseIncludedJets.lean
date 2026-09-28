import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M47.LimitNoncollapseGeneralizedJets
import PoincareConjecture.Proofs.M34.Standard.IncludedMetricCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.LocalSpatialJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem limitNoncollapse_generalized_coefficient_contDiffOn
    (P : M47Predecessors.{u}) {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {G : GeneralizedRicciFlowData.{u}} {b Q τ : ℝ} (hτ : 0 < τ)
    (U : TopologicalSpace.Opens L.sliceCarrier.carrier)
    (hne : (U : Set L.sliceCarrier.carrier).Nonempty)
    (e : GeneralizedFlowCylinder G L.sliceCarrier b Q (Icc (-τ) 0) U)
    (q : L.sliceCarrier.carrier) (a b' : Fin 3) :
    ContDiffOn ℝ ∞ (blowupPullbackCoefficient e q a b')
      (Icc (-τ) 0 ×ˢ ((extChartAt (𝓡 3) q).target ∩
        (extChartAt (𝓡 3) q).symm ⁻¹' U)) := by
  classical
  obtain ⟨F, hF⟩ := terminalSourceRealization_generalized P hτ U hne e
  let c := extChartAt (𝓡 3) q
  let W := c.target ∩ c.symm ⁻¹' (U : Set L.sliceCarrier.carrier)
  let i := U.openPartialHomeomorphSubtypeCoe (show Nonempty U from ⟨⟨hne.choose, hne.choose_spec⟩⟩)
  let φ : E → U := i.symm ∘ c.symm
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) U.isOpen
  have hval {x : E} (hx : x ∈ W) : (φ x).val = c.symm x :=
    i.right_inv (by
      rw [U.openPartialHomeomorphSubtypeCoe_target]
      exact hx.2)
  have heq {x : E} (hx : x ∈ W) :
      (fun y => (φ y).val) =ᶠ[𝓝 x] c.symm :=
    Filter.mem_of_superset (hW.mem_nhds hx) (fun _ hy => hval hy)
  have hc {x : E} (hx : x ∈ W) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
      (extChartAt_target_mem_nhds' hx.1)
  have hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U φ x).mp
    exact (hc hx).congr_of_eventuallyEq (heq hx)
  have hcoeff := F.contDiffOn_clock_spatialPullback_inner hW hφ
    contDiff_id (fun _ hs => hs)
    (EuclideanSpace.basisFun (Fin 3) ℝ a)
    (EuclideanSpace.basisFun (Fin 3) ℝ b')
  apply hcoeff.congr
  intro z hz
  have hp := (hφ z.2 hz.2).contMDiffAt (hW.mem_nhds hz.2)
  have hd := mfderiv_comp z.2
    ((contMDiff_subtype_val (n := ∞) (φ z.2)).mdifferentiableAt (by simp))
    (hp.mdifferentiableAt (by simp))
  have hdc := (heq hz.2).mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  change mfderiv (𝓡 3) (𝓡 3) (fun y => (φ y).val) z.2 = _ at hd
  have hm := (hF z.1 hz.1 (φ z.2)).1
    (mfderiv (𝓡 3) (𝓡 3) φ z.2 (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) φ z.2 (EuclideanSpace.basisFun (Fin 3) ℝ b'))
  have hv (v : E) :
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) (φ z.2)
        (mfderiv (𝓡 3) (𝓡 3) φ z.2 v) =
      mfderiv (𝓡 3) (𝓡 3) c.symm z.2 v :=
    congrArg (fun A => A v) (hd.symm.trans hdc)
  rw [hv, hv, hval hz.2] at hm
  simpa only [blowupPullbackCoefficient, dif_pos hz.1, c, id_eq] using hm.symm



theorem limitNoncollapse_generalized_spatial_jet
    (P : M47Predecessors.{u}) {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {G : GeneralizedRicciFlowData.{u}} {b Q τ : ℝ} (hτ : 0 < τ)
    (U : TopologicalSpace.Opens L.sliceCarrier.carrier)
    (hne : (U : Set L.sliceCarrier.carrier).Nonempty)
    (e : GeneralizedFlowCylinder G L.sliceCarrier b Q (Icc (-τ) 0) U)
    (q : L.sliceCarrier.carrier) (r : ℕ) (a b' : Fin 3) (z : ℝ × E)
    (hz : z.1 ∈ Icc (-τ) 0 ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ U) :
    iteratedFDeriv ℝ r (fun y => blowupPullbackCoefficient e q a b' (z.1, y)) z.2 =
      (iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e q a b')
        (Icc (-τ) 0 ×ˢ (extChartAt (𝓡 3) q).target) z).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  exact iteratedFDeriv_prod_slice_eq_within_of_open_subset
    (limitNoncollapse_generalized_coefficient_contDiffOn P hτ U hne e q a b')
    (uniqueDiffOn_Icc (neg_lt_zero.mpr hτ))
    ((continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) U.isOpen)
    inter_subset_left hz.1 hz.2 (WithTop.coe_le_coe.mpr le_top)

section Convergence

variable (P : M47Predecessors.{u}) {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier :=
  C.limit.carrier.topologicalSpace
local instance : ChartedSpace E C.limit.carrier.carrier := C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

include P




theorem limitNoncollapse_generalized_compact_spatial_jets
    (hJ : UniqueDiffOn ℝ J) (q : C.limit.sliceCarrier.carrier) (r : ℕ)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    {H : Set E} (hH : IsCompact H) (hHt : H ⊆ (extChartAt (𝓡 3) q).target)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      Ktime ⊆ Icc (-C.exhaustion.time k) 0 ∧
      (extChartAt (𝓡 3) q).symm '' H ⊆ C.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ y ∈ H, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ r
            (fun z => blowupPullbackCoefficient (C.embedding k) q a b (s, z)) y -
          iteratedFDeriv ℝ r
            (fun z => FlowCarrier.coordinateCoefficient C.limit.carrier q
              (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (s, z)) y‖ <
          epsilon := by
  let c := extChartAt (𝓡 3) q
  have hc : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hHt)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset hc
  have hdom : Ktime ×ˢ H ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      c.symm z.2 ∈ C.exhaustion.space j} := by
    intro z hz
    exact ⟨⟨hKJ hz.1, hHt hz.2⟩, hj ⟨z.2, hz.2, rfl⟩⟩
  obtain ⟨N, hjN, hN⟩ := limitNoncollapse_generalized_uniform_spatialJetWithin
    C q j r (Ktime ×ˢ H) (hKtime.prod hH) hdom epsilon hepsilon
  filter_upwards [eventually_ge_atTop N,
    C.exhaustion.time_cofinal Ktime hKtime hKJ] with k hk htime
  have hspace : c.symm '' H ⊆ C.exhaustion.space k :=
    hj.trans (C.exhaustion.space_increasing (hjN.trans hk))
  refine ⟨htime, hspace, ?_⟩
  intro s hs y hy a b
  have hsource := limitNoncollapse_generalized_spatial_jet P
    (C.exhaustion.time_pos k)
    (⟨C.exhaustion.space k, C.exhaustion.space_open k⟩ :
      TopologicalSpace.Opens C.limit.sliceCarrier.carrier)
    ⟨C.limit.base, C.exhaustion.base_mem k⟩ (C.embedding k) q r a b (s, y)
    ⟨htime hs, hHt hy, hspace ⟨y, hy, rfl⟩⟩
  have hlimit := iteratedFDeriv_prod_slice_eq_within
    (C.limit.flow.contDiffOn_chartMetric q a b) hJ
    (isOpen_extChartAt_target q) (hKJ hs) (hHt hy)
    (show (r : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [hsource]
  change ‖_ - iteratedFDeriv ℝ r
    (fun z => (C.limit.flow.metric s).inner (c.symm z)
      (mfderiv (𝓡 3) (𝓡 3) c.symm z (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) c.symm z (EuclideanSpace.basisFun (Fin 3) ℝ b))) y‖ < _
  rw [hlimit]
  exact (hN k hk).2 a b (s, y) ⟨hs, hy⟩

end Convergence

end PoincareConjecture.M47
