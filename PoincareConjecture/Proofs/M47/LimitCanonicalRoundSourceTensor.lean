import PoincareConjecture.Proofs.M47.LimitCanonicalRoundParameterJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable local instance roundSourceDualGroup : NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance roundSourceDualSpace : NormedSpace ℝ (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance roundSourceBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance roundSourceBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
  [IsManifold (𝓡 3) ∞ X]




noncomputable def limitCanonicalRoundSourceTensor
    {H : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q : ℝ} {J : Set ℝ} {W : Set C.carrier}
    (e : GeneralizedFlowCylinder H C origin Q J W)
    (i : X → C.carrier) (s : ℝ) (hs : s ∈ J) (c : ℝ) :
    CovariantTensorEvaluation 3 X 2 :=
  fun x v => c * e.pullbackInner s hs (i x)
    (mfderiv (𝓡 3) (𝓡 3) i x (v 0)) (mfderiv (𝓡 3) (𝓡 3) i x (v 1))

omit [IsManifold (𝓡 3) ∞ X] in


theorem limitCanonical_round_source_tensor_eq
    {H : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q : ℝ} {J : Set ℝ} {W : Set C.carrier}
    (e : GeneralizedFlowCylinder H C origin Q J W) (hW : W = univ)
    {i : X → C.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (s : ℝ) (hs : s ∈ J) (c : ℝ) :
    limitCanonicalRoundSourceTensor e i s hs c =
      (fun x v => (c * Q) * (H.metric (origin + s / Q)).inner
        ((e.forward s hs ∘ i) x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ i) x (v 0))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ i) x (v 1))) := by
  have he : ContMDiff (𝓡 3) (𝓡 3) ∞ (e.forward s hs) :=
    contMDiffOn_univ.mp (hW ▸ e.forward_smooth s hs)
  funext x v
  rw [mfderiv_comp x (he.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))]
  change c * (Q * _) = (c * Q) * _
  rw [mul_assoc]
  rfl




theorem limitCanonical_round_source_tensor_smooth
    {H : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q : ℝ} {J : Set ℝ} {W : Set C.carrier}
    (e : GeneralizedFlowCylinder H C origin Q J W) (hW : W = univ)
    {i : X → C.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (s : ℝ) (hs : s ∈ J) (c : ℝ) :
    IsSmoothCovariantTensor (limitCanonicalRoundSourceTensor e i s hs c) := by
  rw [limitCanonical_round_source_tensor_eq e hW hi]
  have he : ContMDiff (𝓡 3) (𝓡 3) ∞ (e.forward s hs) :=
    contMDiffOn_univ.mp (hW ▸ e.forward_smooth s hs)
  exact (M44.isSmoothCovariantTensor_metric_pullback
    (H.metric (origin + s / Q)) (he.comp hi)).const_mul (c * Q)

omit [IsManifold (𝓡 3) ∞ X] in


theorem limitCanonical_round_source_parameter_readout
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin Q : ℝ} {I : Set ℝ} {W : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin Q I W)
    (q : L.sliceCarrier.carrier) (s c : ℝ) (hs : s ∈ I)
    {i : X → L.sliceCarrier.carrier} {f : E3 → X} {x : E3}
    (hi : MDifferentiableAt (𝓡 3) (𝓡 3) i (f x))
    (hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x)
    (hq : i (f x) ∈ (extChartAt (𝓡 3) q).source) (v : Fin 2 → E3) :
    limitCanonicalRoundParameterField e q s c (i ∘ f) x (v 0) (v 1) =
      limitCanonicalRoundSourceTensor e i s hs c (f x)
        (fun a => mfderiv (𝓡 3) (𝓡 3) f x (v a)) := by
  rw [limitCanonical_round_parameter_readout e q s c hs (hi.comp x hf) hq]
  rw [mfderiv_comp x hi hf]
  rfl



theorem limitCanonical_round_parameter_smooth
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin Q : ℝ} {I : Set ℝ} {W : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin Q I W) (hW : W = univ)
    (q : L.sliceCarrier.carrier) (s c : ℝ) (hs : s ∈ I)
    {phi : E3 → L.sliceCarrier.carrier} {U : Set E3} (hU : IsOpen U)
    (hphi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi U)
    (hq : MapsTo phi U (extChartAt (𝓡 3) q).source) :
    ContDiffOn ℝ ∞ (limitCanonicalRoundParameterField e q s c phi) U := by
  have he : ContMDiff (𝓡 3) (𝓡 3) ∞ (e.forward s hs) :=
    contMDiffOn_univ.mp (hW ▸ e.forward_smooth s hs)
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.forward s hs ∘ phi) U :=
    he.comp_contMDiffOn hphi
  have hg : ContDiffOn ℝ ∞ (fun x => (c * Q) •
      (H.metric (origin + s / Q)).pullbackCoefficients (e.forward s hs ∘ phi) x) U := by
    apply (ContinuousLinearMap.lsmul ℝ ℝ (E := Bilin) (c * Q)).contDiff.comp_contDiffOn
    intro x hx
    exact ((H.metric (origin + s / Q)).contDiffAt_pullbackCoefficients
      ((hcomp x hx).contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  ext v w
  have hphi' := ((hphi x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  rw [limitCanonical_round_parameter_readout e q s c hs hphi' (hq hx)]
  change c * (Q * _) = (c * Q) *
    (H.metric (origin + s / Q)).inner _
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ phi) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ phi) x w)
  rw [mfderiv_comp x (he.mdifferentiableAt (by simp)) hphi', mul_assoc]
  rfl

end PoincareConjecture.M47
