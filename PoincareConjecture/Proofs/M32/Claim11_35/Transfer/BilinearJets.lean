import PoincareConjecture.Proofs.M32.Claim11_34.SpatialJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

local instance : NormedAddCommGroup (E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private theorem sourceCoefficient_spatial_contDiffAt
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {I : SpacetimeInterval} {origin scale : ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I.domain U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier) (a b : Fin 3)
    {s : ℝ} (hs : s ∈ I.domain) {y : E₃}
    (hy : y ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm y ∈ U) :
    ContDiffAt ℝ ∞ (fun z => blowupPullbackCoefficient e q a b (s, z)) y := by
  let W := (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hslice : ContDiffOn ℝ ∞
      (fun z => blowupPullbackCoefficient e q a b (s, z)) W :=
    (blowupPullbackCoefficient_contDiffOn e hU q a b).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hs, hz⟩)
  exact hslice.contDiffAt (hW.mem_nhds hy)

set_option backward.isDefEq.respectTransparency false in
private theorem limitCoefficient_spatial_contDiffAt
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (q : L.sliceCarrier.carrier)
    (a b : Fin 3) {s : ℝ} (hs : s ∈ J) {y : E₃}
    (hy : y ∈ (extChartAt (𝓡 3) q).target) :
    ContDiffAt ℝ ∞ (fun z => FlowCarrier.coordinateCoefficient L.carrier q
      (fun t x v w => (L.flow.metric t).inner x v w) a b (s, z)) y := by
  have hcoeff := contDiffOn_clock_pullbackCoefficients_of_smoothFamily
    L.flow.smooth (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm (n := ∞) q)
    (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t)) (fun _ ht => ht)
  have hscalar := (hcoeff.clm_apply
    (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  have hslice := hscalar.comp (s := (extChartAt (𝓡 3) q).target)
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => ⟨hs, hz⟩)
  exact hslice.contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)

private theorem bilinear_dual_sum_apply (d : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, d i j •
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)).smulRight
        (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j)))
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      d a b := by
  simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left]

set_option backward.isDefEq.respectTransparency false in

theorem blowup_uniform_bilinear_errorJets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.sliceCarrier.carrier) (j m : ℕ)
    (K : Set (ℝ × E₃)) (hK : IsCompact K)
    (hdom : K ⊆ {z | z ∈ blowupMetricChartDomain G.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    let B : ℕ → ℝ → E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun k s y =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        (blowupPullbackCoefficient (G.embedding k) q a b (s, y) -
          FlowCarrier.coordinateCoefficient G.limit.carrier q
            (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (s, y)) •
          (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ a)).smulRight
            (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b))
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-G.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ z ∈ K, ContDiffAt ℝ ∞ (B k z.1) z.2 ∧
        ∀ r ≤ m, ‖iteratedFDeriv ℝ r (B k z.1) z.2‖ < eta := by
  classical
  dsimp only
  choose N hjN hN using fun r : Fin (m + 1) =>
    blowup_uniform_spatial_metricJets G q j r K hK hdom (eta / 10) (by positivity)
  let N₀ : ℕ := ∑ r : Fin (m + 1), N r
  have hNN (r : Fin (m + 1)) : N r ≤ N₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  refine ⟨N₀, (hjN 0).trans (hNN 0), fun k hk => ?_⟩
  refine ⟨(hN 0 k ((hNN 0).trans hk)).1, fun z hz => ?_⟩
  have hzsource := (hN 0 k ((hNN 0).trans hk)).1 hz
  have hzlimit := (hdom hz).1
  let Itime : SpacetimeInterval := {
    domain := Icc (-G.exhaustion.time k) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-G.exhaustion.time k,
      ⟨le_rfl, neg_nonpos.mpr (G.exhaustion.time_pos k).le⟩,
      0, ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩,
      (neg_lt_zero.mpr (G.exhaustion.time_pos k)).ne⟩ }
  have hs (a b : Fin 3) : ContDiffAt ℝ ∞
      (fun y => blowupPullbackCoefficient (G.embedding k) q a b (z.1, y)) z.2 :=
    sourceCoefficient_spatial_contDiffAt (I := Itime) (G.embedding k)
      (G.exhaustion.space_open k) q a b hzsource.1
      ⟨hzsource.2, G.exhaustion.space_increasing
        (((hjN 0).trans (hNN 0)).trans hk) (hdom hz).2⟩
  have hl (a b : Fin 3) : ContDiffAt ℝ ∞
      (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2 :=
    limitCoefficient_spatial_contDiffAt G.limit q a b hzlimit.1 hzlimit.2
  let d := fun y a b => blowupPullbackCoefficient (G.embedding k) q a b (z.1, y) -
    FlowCarrier.coordinateCoefficient G.limit.carrier q
      (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (z.1, y)
  let B : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    ∑ a : Fin 3, ∑ b : Fin 3, d y a b •
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ a)).smulRight
        (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b))
  have hB : ContDiffAt ℝ ∞ B z.2 :=
    ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
      ((hs a b).sub (hl a b)).smul contDiffAt_const
  refine ⟨hB, fun r hr => ?_⟩
  let l : Fin (m + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  have hentry (a b : Fin 3) :
      ‖iteratedFDeriv ℝ r (fun y => B y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) z.2‖ ≤
        eta / 10 := by
    have heq : (fun y => B y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) = fun y => d y a b := by
      funext y
      exact bilinear_dual_sum_apply (d y) a b
    rw [heq]
    change ‖iteratedFDeriv ℝ r
      ((fun y => blowupPullbackCoefficient (G.embedding k) q a b (z.1, y)) -
        (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
          (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (z.1, y))) z.2‖ ≤ eta / 10
    rw [iteratedFDeriv_sub_apply ((hs a b).of_le (by exact_mod_cast le_top))
      ((hl a b).of_le (by exact_mod_cast le_top))]
    exact ((hN l k ((hNN l).trans hk)).2 a b z hz).le
  calc
    _ ≤ (3 : ℝ) * 3 * (eta / 10) :=
      SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
        (EuclideanSpace.basisFun (Fin 3) ℝ) hB r hentry
    _ < eta := by linarith

end PoincareConjecture.M32
