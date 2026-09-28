import PoincareConjecture.Proofs.M35.CapGeometry.FullNeckCoordinateJets
import PoincareConjecture.Proofs.M35.CapGeometry.FullNeckTargetMetric
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedFullNeckJets
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_full_neck_coefficient_jets_uniform
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (N : EpsilonNeck (L.limit.flow.metric 0)) (_he : N.epsilon ≤ 1 / 24)
      (_hcompact : IsCompact (closure N.carrier))
      (j : ℕ) (_hstage : closure N.carrier ⊆ L.exhaustion.space j)
      (I : Set ℝ) (_hI : IsCompact I) (_hIt : I ⊆ Iic 0)
      (r : ℕ) (_hr : r ≤ ⌊N.epsilon⁻¹⌋₊) (a b : Fin 3) (eta : ℝ) (_heta : 0 < eta),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      ∃ K : ℕ, ∀ k ≥ K, ∀ u ∈ I, ∀ q : UnitTwoSphere,
        ∀ s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderTensorCoefficient (fun z v w => Q k *
            roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
              (F k ∘ N.coordinate_map) z v w) (chartAt E2 q) y a b -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map)
            (chartAt E2 q) y a b) (0, s)‖ < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : FirstCountableTopology L.limit.carrier.carrier :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  intro N he hcompact j hstage I hI hIt r hr a b eta heta
  classical
  dsimp only
  by_contra hnot
  push Not at hnot
  choose sigma hsigma u hu q s hs hbad using hnot
  have hsig : Tendsto sigma atTop atTop := tendsto_atTop_mono hsigma tendsto_id
  have himages (k : ℕ) : N.coordinate_map (q k, s k) ∈ closure N.carrier :=
    subset_closure (N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hs k⟩)
  obtain ⟨z₀, hz₀, pick, hpick, himage⟩ := hcompact.tendsto_subseq himages
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from z₀)
  obtain ⟨gB, W, hW, hzW, _hWtarget, hmetric⟩ :=
    (L.limit.flow.metric 0).exists_normalized_chart_realization
      (N.scale⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr N.scale_pos)) z₀
  let V := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
  have hV : IsOpen V := (continuousOn_extChartAt_symm
    (show L.limit.carrier.carrier from z₀)).isOpen_inter_preimage
      (isOpen_extChartAt_target (show L.limit.carrier.carrier from z₀))
      (L.exhaustion.space_open j)
  have hzV : c z₀ ∈ V := ⟨mem_extChartAt_target (show L.limit.carrier.carrier from z₀),
    (congrArg (fun z : L.limit.sliceCarrier.carrier => z ∈ L.exhaustion.space j)
      (c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from z₀)))).mpr
        (hstage hz₀)⟩
  obtain ⟨C, hC, hzC, hCV⟩ := exists_compact_between isCompact_singleton (hV.inter hW)
    (singleton_subset_iff.mpr ⟨hzV, hzW⟩)
  have hchart : ContinuousAt c z₀ :=
    (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞) (x := z₀)).continuousAt
  have hnear : ∀ᶠ k in atTop, N.coordinate_map (q (pick k), s (pick k)) ∈ c.source ∧
      c (N.coordinate_map (q (pick k), s (pick k))) ∈ interior C :=
    (himage.eventually ((isOpen_extChartAt_source
      (show L.limit.carrier.carrier from z₀)).mem_nhds
        (mem_extChartAt_source (show L.limit.carrier.carrier from z₀)))).and
      ((hchart.tendsto.comp himage).eventually
        (isOpen_interior.mem_nhds (hzC (mem_singleton _))))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hnear
  let tail (k : ℕ) := pick (k + K)
  have htail : Tendsto tail atTop atTop := hpick.tendsto_atTop.comp (tendsto_add_atTop_nat K)
  have hret (k : ℕ) : N.coordinate_map (q (tail k), s (tail k)) ∈ c.source ∧
      c (N.coordinate_map (q (tail k), s (tail k))) ∈ C :=
    ⟨(hK (k + K) (Nat.le_add_left _ _)).1,
      interior_subset (hK (k + K) (Nat.le_add_left _ _)).2⟩
  have hBj (k : ℕ) : ∀ᶠ y in 𝓝 (c (N.coordinate_map (q (tail k), s (tail k)))),
      gB.euclideanCoefficients y = N.scale⁻¹ ^ 2 •
        (L.limit.flow.metric 0).pullbackCoefficients c.symm y := by
    filter_upwards [hW.mem_nhds (hCV (hret k).2).2] with y hy
    exact hmetric y hy
  have hjets := N.full_coordinate_jets_of_target_realization he
    (q ∘ tail) (s ∘ tail) (fun k => hs (tail k)) z₀ (fun k => (hret k).1)
    C hC (fun k => (hret k).2) gB hBj
  have hlinear : HasUniformJetBoundsAt (⌊N.epsilon⁻¹⌋₊ + 1)
      (fun _ : ℕ => cylinderCoordinateEquiv.symm) (fun k => (0, s (tail k))) := by
    intro m _
    have hcompact₀ : IsCompact (({0} : Set E2) ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹) :=
      isCompact_singleton.prod isCompact_Icc
    have hl : ContDiff ℝ ∞ (cylinderCoordinateEquiv.symm : RoundCylinderCoordinates → E3) :=
      cylinderCoordinateEquiv.symm.contDiff
    have hjet : Continuous (fun y => iteratedFDeriv ℝ m
        (cylinderCoordinateEquiv.symm : RoundCylinderCoordinates → E3) y) :=
      hl.continuous_iteratedFDeriv (by exact_mod_cast le_top (a := (m : ℕ∞)))
    obtain ⟨B, hB⟩ := hcompact₀.exists_bound_of_continuousOn hjet.continuousOn
    exact ⟨B, fun k => hB _ ⟨mem_singleton _,
      ⟨(hs (tail k)).1.le, (hs (tail k)).2.le⟩⟩⟩
  have hregular (k : ℕ) : ContDiffAt ℝ ∞
      (c ∘ N.coordinate_map ∘ cylinderChart (q (tail k)))
      (cylinderCoordinateEquiv.symm (0, s (tail k))) := by
    have hcenter : cylinderChart (q (tail k))
        (cylinderCoordinateEquiv.symm (0, s (tail k))) = (q (tail k), s (tail k)) := by
      have hq := (chartAt E2 (q (tail k))).left_inv (mem_chart_source E2 (q (tail k)))
      rw [sphere_chart_center] at hq
      simp only [cylinderChart, ContinuousLinearEquiv.apply_symm_apply, hq]
    have hc : N.coordinate_map (cylinderChart (q (tail k))
        (cylinderCoordinateEquiv.symm (0, s (tail k)))) ∈ (chartAt E3 z₀).source := by
      rw [hcenter, ← extChartAt_source (I := 𝓡 3)]
      exact (hret k).1
    have hparam : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (N.coordinate_map ∘ cylinderChart (q (tail k)))
        (cylinderCoordinateEquiv.symm (0, s (tail k))) :=
      (N.full_euclidean_chart_regular (q (tail k)) (by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (tail k))).1
    exact ((contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hc).comp
      (cylinderCoordinateEquiv.symm (0, s (tail k))) hparam).contDiffAt
  have hproductJets : HasUniformJetBoundsAt (r + 1)
      (fun (k : ℕ) (y : RoundCylinderCoordinates) =>
        c (N.coordinate_map ((chartAt E2 (q (tail k))).symm y.1, y.2)))
      (fun k => (0, s (tail k))) := by
    have hh := hlinear.comp hjets
      (fun _ => cylinderCoordinateEquiv.symm.contDiff.contDiffAt) hregular
    have hh' := hh.mono_order (Nat.add_le_add_right hr 1)
    simpa only [Function.comp_def, cylinderChart,
      ContinuousLinearEquiv.apply_symm_apply] using hh'
  have hKU : I ×ˢ C ⊆ {p | p ∈ blowupMetricChartDomain L.limit z₀ ∧
      c.symm p.2 ∈ L.exhaustion.space j} := by
    intro p hp
    refine ⟨⟨?_, (hCV hp.2).1.1⟩, (hCV hp.2).1.2⟩
    simpa [blowupBackwardInterval] using hIt hp.1
  have hlim := blowupSequence_neck_coefficient_error_jets_of_bounded P E t x ht hR L
    N.coordinate_map (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (isOpen_univ.prod isOpen_Ioo) N.coordinate_map_smooth
    (q ∘ tail) (s ∘ tail) (fun k => ⟨mem_univ _, hs (tail k)⟩)
    z₀ (fun k => (hret k).1) j (I ×ˢ C) (hI.prod hC) hKU
    (sigma ∘ tail) (hsig.comp htail) (u ∘ tail)
    (fun k => ⟨hu (tail k), (hret k).2⟩) r a b hproductJets
  have hnorm := hlim.norm
  rw [norm_zero] at hnorm
  exact (not_le.mpr heta) (ge_of_tendsto hnorm
    (Eventually.of_forall (fun k => hbad (tail k))))

end PoincareConjecture.M35.OrdinaryRealization
