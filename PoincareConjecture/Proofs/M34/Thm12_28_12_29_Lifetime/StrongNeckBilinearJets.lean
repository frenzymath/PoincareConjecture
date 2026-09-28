import PoincareConjecture.Proofs.M34.Mathlib.NeckFiniteBilinearJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.UniformOrdinarySpatialJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)



noncomputable def blowupCoordinateBilinear
    {G : GeneralizedRicciFlowData.{u}} {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (q : L.sliceCarrier.carrier) (s : ℝ) (y : E₃) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
    (fun a b => blowupPullbackCoefficient e q a b (s, y))



noncomputable def limitCoordinateBilinear
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (q : L.sliceCarrier.carrier)
    (s : ℝ) (y : E₃) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := by
  let := L.carrier.topologicalSpace
  let := L.carrier.chartedSpace
  let := L.carrier.isManifold
  exact ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
    (fun a b => FlowCarrier.coordinateCoefficient L.carrier q
      (fun t x v w => (L.flow.metric t).inner x v w) a b (s, y))

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R



theorem ordinaryChapter11Cylinder_coefficient_spatial_contDiffAt
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder (G) L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K) {s : ℝ} (hs : s ∈ K)
    (q : L.sliceCarrier.carrier) (a b : Fin 3) {y : E₃}
    (hy : y ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm y ∈ U) :
    ContDiffAt ℝ ∞ (fun z => blowupPullbackCoefficient e q a b (s, z)) y := by
  let W := (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hslice : ContDiffOn ℝ ∞
      (fun z => blowupPullbackCoefficient e q a b (s, z)) W :=
    (ordinaryChapter11Cylinder_coefficient_contDiffOn R e hU hK hs q a b).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hs, hz⟩)
  exact hslice.contDiffAt (hW.mem_nhds hy)



theorem ordinaryChapter11_uniform_bilinear_metricJets
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (q : C.limit.sliceCarrier.carrier) (j m : ℕ)
    (K : Set (ℝ × E₃)) (hK : IsCompact K)
    (hdom : K ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ C.exhaustion.space j})
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ z ∈ K, ∀ r ≤ m,
        ‖iteratedFDeriv ℝ r (fun y => blowupCoordinateBilinear (C.embedding k) q z.1 y -
          limitCoordinateBilinear C.limit q z.1 y) z.2‖ < epsilon := by
  classical
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  obtain ⟨B, hB, hb⟩ := exists_piLpBilinearFromCoordinates_jet_bound
    (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin 3) (J := Fin 3) (E := E₃) (F := ℝ)
  let eta : ℝ := epsilon / (B + 1)
  have heta : 0 < eta := div_pos hepsilon (by linarith)
  have hscale : (B + 1) * eta = epsilon := by
    dsimp [eta]
    field_simp
  have hsmall : B * eta < epsilon := by nlinarith
  choose N hjN hN using fun r : Fin (m + 1) =>
    ordinaryChapter11_uniform_spatial_metricJets R p hpositive hdiverges C hJ q j r
      K hK hdom eta heta
  let N₀ : ℕ := ∑ r : Fin (m + 1), N r
  have hNN (r : Fin (m + 1)) : N r ≤ N₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  refine ⟨N₀, (hjN 0).trans (hNN 0), ?_⟩
  intro k hk
  refine ⟨(hN 0 k ((hNN 0).trans hk)).1, ?_⟩
  intro z hz r hr
  let l : Fin (m + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  have hkn : N l ≤ k := (hNN l).trans hk
  have hzsource := (hN l k hkn).1 hz
  have hzlimit := (hdom hz).1
  have hjk : j ≤ k := (hjN l).trans hkn
  have hs (a b : Fin 3) : ContDiffAt ℝ ∞
      (fun y => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y)) z.2 :=
    ordinaryChapter11Cylinder_coefficient_spatial_contDiffAt R (C.embedding k)
      (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected hzsource.1 q a b
      ⟨hzsource.2, C.exhaustion.space_increasing hjk (hdom hz).2⟩
  have hl (a b : Fin 3) : ContDiffAt ℝ ∞
      (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
        (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2 := by
    have hslice := (C.limit.flow.contDiffOn_chartMetric q a b).comp
      (s := (extChartAt (𝓡 3) q).target)
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨hzlimit.1, hy⟩)
    exact hslice.contDiffAt ((isOpen_extChartAt_target q).mem_nhds hzlimit.2)
  let f := fun y a b => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y) -
    FlowCarrier.coordinateCoefficient C.limit.carrier q
      (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)
  have hf (a b : Fin 3) : ContDiffAt ℝ r (fun y => f y a b) z.2 :=
    ((hs a b).sub (hl a b)).of_le (by exact_mod_cast le_top)
  have hfjet (a b : Fin 3) : ‖iteratedFDeriv ℝ r (fun y => f y a b) z.2‖ ≤ eta := by
    change ‖iteratedFDeriv ℝ r
      ((fun y => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y)) -
        (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y))) z.2‖ ≤ eta
    rw [iteratedFDeriv_sub_apply ((hs a b).of_le (by exact_mod_cast le_top))
      ((hl a b).of_le (by exact_mod_cast le_top))]
    exact ((hN l k hkn).2 a b z hz).le
  have heq : (fun y => blowupCoordinateBilinear (C.embedding k) q z.1 y -
      limitCoordinateBilinear C.limit q z.1 y) =
      (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
        (p := 2) (q := 2) (𝕜 := ℝ) (f y)) := by
    funext y
    exact (map_sub (ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)) _ _).symm
  rw [heq]
  exact (hb r f z.2 hf eta hfjet).trans_lt hsmall

end PoincareConjecture.M34
