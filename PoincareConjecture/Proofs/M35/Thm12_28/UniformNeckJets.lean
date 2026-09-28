import PoincareConjecture.Proofs.M35.Thm12_28.SelectedNeckJets









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)



theorem blowupSequence_neck_coefficient_jets_uniform (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : RoundCylinderSpace → L.limit.sliceCarrier.carrier)
      (U : Set RoundCylinderSpace) (_hU : IsOpen U)
      (_hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate U)
      (l : ℝ) (_hdom : univ ×ˢ Icc (-l) l ⊆ U)
      (j : ℕ) (_hspace : ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-l) l,
        coordinate (q, s) ∈ L.exhaustion.space j)
      (I : Set ℝ) (_hI : IsCompact I) (_hIt : I ⊆ Iic 0)
      (r : ℕ) (a b : Fin 3) (eta : ℝ) (_heta : 0 < eta),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      ∃ N : ℕ, ∀ k ≥ N, ∀ u ∈ I, ∀ q : UnitTwoSphere, ∀ s ∈ Icc (-l) l,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderTensorCoefficient (fun z v w => Q k *
            roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
              (F k ∘ coordinate) z v w) (chartAt E2 q) y a b -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (L.limit.flow.metric u) coordinate)
            (chartAt E2 q) y a b) (0, s)‖ < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate U hU hcoord l hdom j hspace I hI hIt r a b eta heta
  classical
  dsimp only
  by_contra hnot
  push Not at hnot
  choose sigma hsigma u hu q s hs hbad using hnot
  have hsig : Tendsto sigma atTop atTop := tendsto_atTop_mono hsigma tendsto_id
  obtain ⟨s₀, hs₀, alpha, halpha, hslim⟩ := isCompact_Icc.tendsto_subseq hs
  obtain ⟨q₀, frame, rho, hrho, hqlim, hframe, _horth, _hjets⟩ :=
    sphere_chart_inverse_subsequence (q ∘ alpha)
  let pick (k : ℕ) := alpha (rho k)
  have hpick : Tendsto pick atTop atTop := halpha.tendsto_atTop.comp hrho.tendsto_atTop
  have hq : Tendsto (fun k => q (pick k)) atTop (𝓝 q₀) := hqlim
  have hsl : Tendsto (fun k => s (pick k)) atTop (𝓝 s₀) :=
    hslim.comp hrho.tendsto_atTop
  have hp₀ : (q₀, s₀) ∈ U := hdom ⟨mem_univ _, hs₀⟩
  let z₀ : L.limit.sliceCarrier.carrier := coordinate (q₀, s₀)
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from z₀)
  let V := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
  have hV : IsOpen V := (continuousOn_extChartAt_symm
    (show L.limit.carrier.carrier from z₀)).isOpen_inter_preimage
      (isOpen_extChartAt_target (show L.limit.carrier.carrier from z₀))
      (L.exhaustion.space_open j)
  have hzV : c z₀ ∈ V := ⟨mem_extChartAt_target (show L.limit.carrier.carrier from z₀),
    (congrArg (fun z : L.limit.sliceCarrier.carrier => z ∈ L.exhaustion.space j)
      (c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from z₀)))).mpr
        (hspace q₀ s₀ hs₀)⟩
  obtain ⟨C, hC, hzC, hCV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hzV)
  have himage : Tendsto (fun k => coordinate (q (pick k), s (pick k))) atTop (𝓝 z₀) :=
    (hcoord.contMDiffAt (hU.mem_nhds hp₀)).continuousAt.tendsto.comp (hq.prodMk_nhds hsl)
  have hchart : ContinuousAt c z₀ :=
    (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞) (x := z₀)).continuousAt
  have hnear : ∀ᶠ k in atTop, coordinate (q (pick k), s (pick k)) ∈ c.source ∧
      c (coordinate (q (pick k), s (pick k))) ∈ interior C :=
    (himage.eventually ((isOpen_extChartAt_source
      (show L.limit.carrier.carrier from z₀)).mem_nhds
        (mem_extChartAt_source (show L.limit.carrier.carrier from z₀)))).and
      ((hchart.tendsto.comp himage).eventually
        (isOpen_interior.mem_nhds (hzC (mem_singleton _))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
  let tail (k : ℕ) := pick (k + N)
  have htail : Tendsto tail atTop atTop := hpick.comp (tendsto_add_atTop_nat N)
  have hret (k : ℕ) : coordinate (q (tail k), s (tail k)) ∈ c.source ∧
      c (coordinate (q (tail k), s (tail k))) ∈ C :=
    ⟨(hN (k + N) (Nat.le_add_left _ _)).1,
      interior_subset (hN (k + N) (Nat.le_add_left _ _)).2⟩
  have hKU : I ×ˢ C ⊆ {p | p ∈ blowupMetricChartDomain L.limit z₀ ∧
      c.symm p.2 ∈ L.exhaustion.space j} := by
    intro p hp
    refine ⟨⟨?_, (hCV hp.2).1⟩, (hCV hp.2).2⟩
    simpa [blowupBackwardInterval] using hIt hp.1
  have hlim := blowupSequence_neck_coefficient_error_jets P E t x ht hR L
    coordinate U hU hcoord (q ∘ tail) q₀ frame
    (hq.comp (tendsto_add_atTop_nat N)) (hframe.comp (tendsto_add_atTop_nat N))
    (s ∘ tail) s₀ (hsl.comp (tendsto_add_atTop_nat N)) hp₀
    (fun k => hdom ⟨mem_univ _, hs (tail k)⟩) z₀
    (mem_extChartAt_source (show L.limit.carrier.carrier from z₀))
    (fun k => (hret k).1) j (I ×ˢ C) (hI.prod hC) hKU
    (sigma ∘ tail) (hsig.comp htail) (u ∘ tail)
    (fun k => ⟨hu (tail k), (hret k).2⟩) r a b
  have hnorm := hlim.norm
  rw [norm_zero] at hnorm
  exact (not_le.mpr heta) (ge_of_tendsto hnorm
    (Eventually.of_forall (fun k => hbad (tail k))))

end PoincareConjecture.M35.OrdinaryRealization
