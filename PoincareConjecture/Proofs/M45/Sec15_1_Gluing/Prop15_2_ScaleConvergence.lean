import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Countersequence
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_SequenceJets
import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.NativeJetConvergence
import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderTimeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance : NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem recent_centered_scalar {epsilon beta : ℝ}
    (I : M45NeckGluingInput.{u} epsilon beta)
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2)
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹) (t : ℝ) :
    jetScalarCurvature (metricTwoJet
      (centeredCylinderMetric
        (roundCylinderPullback (I.recent_flow.metric t) I.recent_patch.coordinate) z.1 z.2) 0) =
      (I.recent_flow.connection t).scalarCurvature (I.recent_patch.coordinate z) := by
  let N := I.recentNeck hpos hsmall
  let A := I.recentCenteredMap z
  let U := centeredNeckDomain N z.2
  have hU : IsOpen U := centeredNeckDomain_isOpen N z.2
  have hx : (0 : E) ∈ U := zero_mem_centeredNeckDomain N hz
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A U :=
    fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).contMDiffWithinAt
  have hi (p : E) (hp : p ∈ U) : (mfderiv (𝓡 3) (𝓡 3) A p).IsInvertible :=
    centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hp
  have hcoeff := eventually_of_mem (hU.mem_nhds hx)
    (fun p hp => I.recentCenteredMap_pullbackCoefficients hpos hsmall z t hp)
  have h := jetScalarCurvature_pullbackCoefficients
    (I.recent_flow.metric t) (I.recent_flow.connection t) hU hA hi hx
  rw [(metricTwoJet_eventuallyEq hcoeff).self_of_nhds] at h
  simpa only [A, M45NeckGluingInput.recentCenteredMap, Function.comp_apply,
    centeredCylinderLift_zero] using h

theorem GluingBadSequence.joining_pointJetsConverge {epsilon d : ℝ}
    (S : GluingBadSequence.{u} epsilon) (hepsilon : 0 < epsilon)
    (hd : Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d))
    (z : ℕ → RoundCylinderSpace)
    (hz : ∀ n, (z n).2 ∈ Ioo (-(S.beta n * epsilon)⁻¹) (S.beta n * epsilon)⁻¹) :
    PointJetsConverge
      (fun n => centeredCylinderMetric
        (roundCylinderPullback ((S.input n).recent_flow.metric (-(S.input n).recent_duration))
          (S.input n).recent_patch.coordinate) (z n).1 (z n).2)
      (fun _ => 0) (evolvingCylinderModelField (-d)) 0 atTop := by
  have he (n : ℕ) : 0 < S.beta n * epsilon := mul_pos (S.beta_pos n) hepsilon
  have he0 : Tendsto (fun n => S.beta n * epsilon) atTop (𝓝 0) := by
    simpa only [zero_mul] using S.beta_tendsto_zero.mul_const epsilon
  have htime (n : ℕ) : -(S.input n).recent_duration ∈ Icc (-1 : ℝ) 0 :=
    ⟨neg_le_neg (S.recent_short n).le, neg_nonpos.mpr (S.input n).recent_duration_pos.le⟩
  have hB (n : ℕ) : RoundCylinderClose (S.beta n * epsilon) (-(S.input n).recent_duration)
      (roundCylinderPullback ((S.input n).recent_flow.metric (-(S.input n).recent_duration))
        (S.input n).recent_patch.coordinate) := by
    obtain ⟨hs, bound, hbound, hjets⟩ := (S.input n).recent_comparison
    have ht : -(S.input n).recent_duration ∈ Icc (-(S.input n).recent_duration) (0 : ℝ) :=
      ⟨le_rfl, neg_nonpos.mpr (S.input n).recent_duration_pos.le⟩
    exact ⟨hs _ ht, bound, hbound, hjets _ ht⟩
  have herror := evolvingCylinderError_pointJetsVanish he he0 htime hB hz
  have hmodel : PointJetsConverge (fun n => evolvingCylinderModelField
      (-(S.input n).recent_duration)) (fun _ => 0) (evolvingCylinderModelField (-d)) 0 atTop :=
    fun m => (continuous_model_evolvingCylinder_iteratedFDeriv m 0).continuousAt.tendsto.comp hd.neg
  exact hmodel.of_sub_vanish herror
    (fun n => evolving_centeredCylinderMetric_contDiffAt (hB n) (z n) (hz n))
    (fun n => (evolvingCylinderModelField_contDiff _).contDiffAt)

theorem GluingBadSequence.scale_sq_tendsto {epsilon d : ℝ}
    (S : GluingBadSequence.{u} epsilon) (hepsilon : 0 < epsilon) (hd0 : 0 ≤ d)
    (hd : Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d)) :
    Tendsto (fun n => (S.input n).older_neck.neck.scale ^ 2) atTop (𝓝 (1 + d)) := by
  classical
  choose q hq using fun n => (S.input n).recent_patch.center_sphere
  let z : ℕ → RoundCylinderSpace := fun n => (q n, 0)
  have he (n : ℕ) : 0 < S.beta n * epsilon := mul_pos (S.beta_pos n) hepsilon
  have hz (n : ℕ) : (z n).2 ∈ Ioo (-(S.beta n * epsilon)⁻¹) (S.beta n * epsilon)⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr (he n)), inv_pos.mpr (he n)⟩
  let A := fun n => centeredCylinderMetric
    (roundCylinderPullback ((S.input n).recent_flow.metric (-(S.input n).recent_duration))
      (S.input n).recent_patch.coordinate) (z n).1 (z n).2
  have hA := S.joining_pointJetsConverge hepsilon hd z hz
  have hAs (n : ℕ) : ContDiffAt ℝ ∞ (A n) 0 := by
    have hp := he n
    let N := (S.input n).recentNeck hp (S.tolerance_lt_half n)
    have hx := zero_mem_centeredNeckDomain N (hz n)
    have h := ((S.input n).recent_flow.metric
      (-(S.input n).recent_duration)).contDiffAt_pullbackCoefficients
        (centeredNeckLift_contMDiffAt N (q n) 0 hx)
    apply h.congr_of_eventuallyEq
    filter_upwards [(centeredNeckDomain_isOpen N 0).mem_nhds hx] with p hp
    exact ((S.input n).recentCenteredMap_pullbackCoefficients
      (he n) (S.tolerance_lt_half n) (z n) (-(S.input n).recent_duration) hp).symm
  have hmodel := (evolvingCylinderModelField_contDiff (-d)).contDiffAt (x := (0 : E))
  have hd1 : -d < 1 := by linarith
  have hscalar := (contDiffAt_jetScalarCurvature (n := 3)
    (J := metricTwoJet (evolvingCylinderModelField (-d)) 0)
    (model_evolvingCylinderField_isInvertible hd1 0)).continuousAt.tendsto.comp
      ((hA.metricTwoJet hAs hmodel).values)
  have hread (n : ℕ) := recent_centered_scalar (S.input n) (he n)
    (S.tolerance_lt_half n) (z n) (hz n) (-(S.input n).recent_duration)
  have hqconv : Tendsto
      (fun n => ((S.input n).recent_flow.connection
        (-(S.input n).recent_duration)).scalarCurvature (S.input n).center)
      atTop (𝓝 ((1 + d)⁻¹)) := by
    simpa only [Function.comp_def, hread, z, hq, model_evolvingCylinder_scalar hd1,
      sub_neg_eq_add] using hscalar
  have hnonzero : (1 + d)⁻¹ ≠ (0 : ℝ) := inv_ne_zero (by linarith)
  have hr := hqconv.inv₀ hnonzero
  simpa only [M45NeckGluingInput.older_scale_sq, inv_inv] using hr

end PoincareConjecture.M45
