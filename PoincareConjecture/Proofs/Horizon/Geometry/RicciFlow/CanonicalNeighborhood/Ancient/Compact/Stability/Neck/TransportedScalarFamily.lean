import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainFamilyComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainSmoothness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.CenteredError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.FullDomainEvolving
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.FullDomainScalarNormalized












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_terminalNeck_full_scalarNormalized_centeredErrorJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (a b : ℝ) (x : G.limit.carrier.carrier),
      a ≤ 0 → b ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (a, x)).2 = ((e k).toFun (b, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {r : ℝ} (hr : 0 < r) {ι : Type*} {l : Filter ι}
    (index : ι → ℕ) (hindex : Tendsto index l atTop)
    {s : ι → ℝ} (hs : Tendsto s l (𝓝 r)) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in l, ∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun p =>
          centeredCylinderError (fun z v w => s i *
            roundCylinderPullback ((S.term (G.subsequence (index i))).flow.flow.metric (u / s i))
              (G.terminalNeckEmbedding e N N.epsilon (index i)) z v w) z.1 z.2 p -
          centeredCylinderError (fun z v w => r *
            roundCylinderPullback (G.limit.flow.flow.metric (u / r))
              N.coordinate_map z v w) z.1 z.2 p) 0‖ ≤ eta := by
  have hdelta : 0 < eta / (4 * r) := div_pos heta (mul_pos (by norm_num) hr)
  have hband : ∀ᶠ i in l, s i ∈ Icc (r / 2) (2 * r) :=
    hs.eventually (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [hband,
    hindex.eventually (hconv.eventually_centeredNeck_jets_full_domain_uniform_time_on_compact
      hfixed N hcompact hsmall (J := Icc (-2 / r) 0) isCompact_Icc
      (fun _ ht => ht.2) hdelta),
    G.limit.flow.flow.eventually_scalarNormalized_centeredNeck_jets_full_domain_uniform_time
      N hcompact hsmall hr hs (half_pos heta),
    hindex.eventually (G.eventually_terminalNeckEmbedding_full e N hcompact)]
    with i hsi hraw hlimit hcoords u hu z hz j hj
  have hpos : 0 < s i := (half_pos hr).trans_le hsi.1
  have htime : u / s i ∈ Icc (-2 / r) 0 := by
    refine ⟨(le_div_iff₀ hpos).mpr ?_, div_nonpos_of_nonpos_of_nonneg hu.2 hpos.le⟩
    have hneg : -2 / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hr.le
    have hbound := mul_le_mul_of_nonpos_left hsi.1 hneg
    have heq : (-2 / r) * (r / 2) = (-1 : ℝ) := by field_simp
    rw [heq] at hbound
    exact hbound.trans hu.1.le
  rw [centeredCylinderError_difference_jet_eq
    ((S.term (G.subsequence (index i))).flow.flow.metric (u / s i))
    (G.limit.flow.flow.metric (u / r))
    (G.terminalNeckEmbedding e N N.epsilon (index i)) N.coordinate_map
    (s i) r z.1 z.2 (isOpen_univ.prod isOpen_Ioo) ⟨mem_univ _, hz⟩
    hcoords.2.2.1 N.coordinate_map_smooth j]
  let f := centeredNeckLift N z.1 z.2
  let fsource := (G.terminalNeckEmbedding e N N.epsilon (index i)) ∘
    centeredCylinderLift z.1 z.2
  let A := ((S.term (G.subsequence (index i))).flow.flow.metric (u / s i)).parametrizedCoefficients
    fsource
  let B := (G.limit.flow.flow.metric (u / s i)).parametrizedCoefficients f
  let C := (G.limit.flow.flow.metric (u / r)).parametrizedCoefficients f
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (0 : E) :=
    centeredNeckLift_contMDiffAt N z.1 z.2 (zero_mem_centeredNeckDomain N hz)
  have hzero : centeredCylinderLift z.1 z.2 (0 : E) ∈ N.cylinderDomain := by
    simpa only [centeredCylinderLift_zero] using (show z ∈ N.cylinderDomain from ⟨mem_univ _, hz⟩)
  have hfsource : ContMDiffAt (𝓡 3) (𝓡 3) ∞ fsource (0 : E) :=
    (hcoords.2.2.1.contMDiffAt (N.cylinderDomain_open.mem_nhds hzero)).comp 0
      (centeredCylinderLift_contMDiff z.1 z.2 0)
  have hA : ContDiffAt ℝ ∞ A (0 : E) :=
    ((S.term (G.subsequence (index i))).flow.flow.metric (u / s i)).contDiffAt_parametrizedCoefficients
      hfsource
  have hB : ContDiffAt ℝ ∞ B (0 : E) :=
    (G.limit.flow.flow.metric (u / s i)).contDiffAt_parametrizedCoefficients hf
  have hC : ContDiffAt ℝ ∞ C (0 : E) :=
    (G.limit.flow.flow.metric (u / r)).contDiffAt_parametrizedCoefficients hf
  have hraw' : ‖iteratedFDeriv ℝ j (fun y => A y - B y) 0‖ ≤ eta / (4 * r) :=
    hraw (u / s i) htime z hz j hj
  have hlimit' : ‖iteratedFDeriv ℝ j (fun y => s i • B y - r • C y) 0‖ ≤ eta / 2 :=
    hlimit u ⟨hu.1.le, hu.2⟩ z hz j hj
  change ‖iteratedFDeriv ℝ j (fun y => s i • A y - r • C y) 0‖ ≤ eta
  have hsplit : (fun y => s i • A y - r • C y) =
      (fun y => s i • (A y - B y) + (s i • B y - r • C y)) := by
    funext y
    rw [smul_sub]
    abel
  rw [hsplit, fun_iteratedFDeriv_add_apply
    (((hA.sub hB).const_smul (s i)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)))
    (((hB.const_smul (s i)).sub (hC.const_smul r)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))),
    iteratedFDeriv_const_smul_apply'
      ((hA.sub hB).of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)))]
  calc
    _ ≤ ‖s i • iteratedFDeriv ℝ j (fun y => A y - B y) 0‖ +
        ‖iteratedFDeriv ℝ j (fun y => s i • B y - r • C y) 0‖ := norm_add_le _ _
    _ = s i * ‖iteratedFDeriv ℝ j (fun y => A y - B y) 0‖ +
        ‖iteratedFDeriv ℝ j (fun y => s i • B y - r • C y) 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    _ ≤ (2 * r) * (eta / (4 * r)) + eta / 2 :=
      add_le_add (mul_le_mul hsi.2 hraw' (norm_nonneg _) (by positivity)) hlimit'
    _ = eta := by field_simp; ring



theorem eventually_terminalNeck_full_scalarNormalized_familyClose
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (a b : ℝ) (x : G.limit.carrier.carrier),
      a ≤ 0 → b ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (a, x)).2 = ((e k).toFun (b, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {r : ℝ} (hr : 0 < r)
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => r * roundCylinderPullback (G.limit.flow.flow.metric (u / r))
        N.coordinate_map z v w))
    {ι : Type*} {l : Filter ι} (index : ι → ℕ) (hindex : Tendsto index l atTop)
    {s : ι → ℝ} (hs : Tendsto s l (𝓝 r)) :
    ∀ᶠ i in l, RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => s i *
        roundCylinderPullback ((S.term (G.subsequence (index i))).flow.flow.metric (u / s i))
          (G.terminalNeckEmbedding e N N.epsilon (index i)) z v w) := by
  apply TerminalNeck.eventually_roundCylinderFamilyClose_of_centeredDifferenceJets_fullDomain
    N.epsilon_pos hclose
  · filter_upwards [hindex.eventually
      (G.eventually_terminalNeck_full_tensorSmoothOn e N hcompact)] with i hi u _
    exact hi (u / s i) (s i)
  · exact fun _ heta => hconv.eventually_terminalNeck_full_scalarNormalized_centeredErrorJets
      hfixed N hcompact hsmall hr index hindex hs heta

end M23TerminalMetricConvergence

end PoincareConjecture
