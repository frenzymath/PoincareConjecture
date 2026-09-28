import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M47.LimitCanonicalRoundCoefficientJets
import PoincareConjecture.Proofs.M13.ConnectionScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable def limitCanonicalNativeChart
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] (q : M) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞ where
  toPartialEquiv := extChartAt (𝓡 3) q
  open_source := isOpen_extChartAt_source q
  open_target := isOpen_extChartAt_target q
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 3) (x := q) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm q

theorem limitCanonical_physical_chart_coefficients
    {H : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder H C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization H F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ H.interval) (q : C.carrier) (x : E)
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxu : (extChartAt (𝓡 3) q).symm x ∈ U) :
    RiemannianMetric.pullbackCoefficients
        (M13.scaleSmoothMetric (F.metric (origin + s / scale)) scale e.scale_pos)
          (limitCanonicalPhysicalChart e hU R s hs ht ∘ (extChartAt (𝓡 3) q).symm) x =
      limitNoncollapseChartForm e q s hs x := by
  let f := limitCanonicalPhysicalChart e hU R s hs ht
  have hf := f.mdifferentiableAt (by simp)
    (show (extChartAt (𝓡 3) q).symm x ∈ f.source by
      rw [limitCanonicalPhysicalChart_source]
      exact hxu)
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hx)).mdifferentiableAt (by simp)
  ext v w
  rw [limitNoncollapseChartForm_apply e hU q s hs x hx hxu]
  change scale * (F.metric (origin + s / scale)).inner
      (f ((extChartAt (𝓡 3) q).symm x))
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ (extChartAt (𝓡 3) q).symm) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ (extChartAt (𝓡 3) q).symm) x w) = _
  rw [mfderiv_comp x hf hc]
  exact limitCanonicalPhysicalChart_metric e hU R s hs ht hxu _ _

section ActualSequence

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_terminal_clock_mem (k : ℕ) :
    (V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k) ∈
      (V.flow (G.subsequence k)).interval :=
  ((V.flow (G.subsequence k)).slice_nonempty_iff _).mp
    ⟨(G.embedding k).forward 0
      ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ G.limit.base⟩

noncomputable def limitCanonicalPhysicalTerminalChart
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i)) (k : ℕ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier ∞ :=
  limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) 0
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
    (limitCanonical_terminal_clock_mem G k)

theorem limitCanonical_physical_terminal_coefficient_jets
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (q : G.limit.sliceCarrier.carrier) (m : ℕ) {K : Set E}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k)))
            (limitCanonicalPhysicalTerminalChart G F R k ∘ (extChartAt (𝓡 3) q).symm)))
      (iteratedFDeriv ℝ m ((G.limit.flow.metric 0).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm)) atTop K := by
  let c := extChartAt (𝓡 3) q
  have hconv := (limitCanonical_round_bilinear_coefficient_convergence P G q 0
    G.limit.zero_mem).jets m K hK hKc
  have himage : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm q).mono hKc)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  apply hconv.congr
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  have hspace : c.symm '' K ⊆ G.exhaustion.space k :=
    hj.trans (G.exhaustion.space_increasing hk)
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  let W := c.target ∩ c.symm ⁻¹' G.exhaustion.space k
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion.space_open k)
  have hxW : x ∈ W := ⟨hKc hx, hspace (mem_image_of_mem c.symm hx)⟩
  have heq : (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)
      (fun a b : Fin 3 => blowupPullbackCoefficient (G.embedding k) q a b (0, y)))
      =ᶠ[𝓝 x] RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k)))
        (limitCanonicalPhysicalTerminalChart G F R k ∘ c.symm) := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact (limitCanonical_round_reconstructed_eq_chartForm (G.embedding k)
      (G.exhaustion.space_open k) q 0 h0 y hy.1 hy.2).trans
        (limitCanonical_physical_chart_coefficients (G.embedding k)
          (G.exhaustion.space_open k) (R (G.subsequence k)) 0 h0
          (limitCanonical_terminal_clock_mem G k) q y hy.1 hy.2).symm
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

end ActualSequence

end PoincareConjecture.M47
