import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_OlderSamples
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_ScaleConvergence
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_TransitionControl
import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.ActualTransitionData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance transitionSequenceCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance transitionSequenceCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

variable {epsilon : ℝ} (S : GluingBadSequence.{u} epsilon)

noncomputable def GluingBadSequence.transitionData (hepsilon : 0 < epsilon) (n : ℕ) :
    (S.input n).ActualTransitionData (mul_pos (S.beta_pos n) hepsilon)
      (S.tolerance_lt_half n) (S.point n) :=
  Classical.choice ((S.input n).exists_actualTransitionData
    (mul_pos (S.beta_pos n) hepsilon) (S.tolerance_lt_half n)
    (S.point n) (S.recent_point_mem hepsilon n))

theorem GluingBadSequence.joining_error_pointJetsVanish (hepsilon : 0 < epsilon) :
    PointJetsVanish (fun n p =>
      (S.input n).recentCenteredField (S.point n) (-(S.input n).recent_duration) p -
        evolvingCylinderModelField (-(S.input n).recent_duration) p)
      (fun _ => 0) atTop := by
  have he (n : ℕ) : 0 < S.beta n * epsilon := mul_pos (S.beta_pos n) hepsilon
  have he0 : Tendsto (fun n => S.beta n * epsilon) atTop (𝓝 0) := by
    simpa only [zero_mul] using S.beta_tendsto_zero.mul_const epsilon
  apply evolvingCylinderError_pointJetsVanish he he0
    (fun n => ⟨neg_le_neg (S.recent_short n).le,
      neg_nonpos.mpr (S.input n).recent_duration_pos.le⟩) (fun n => ?_)
    (S.recent_point_mem hepsilon)
  obtain ⟨hs, bound, hbound, hjets⟩ := (S.input n).recent_comparison
  have ht : -(S.input n).recent_duration ∈ Icc (-(S.input n).recent_duration) (0 : ℝ) :=
    ⟨le_rfl, neg_nonpos.mpr (S.input n).recent_duration_pos.le⟩
  exact ⟨hs _ ht, bound, hbound, hjets _ ht⟩

theorem GluingBadSequence.transition_jets_bounded (hepsilon : 0 < epsilon)
    {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d)) :
    ∀ m, FinitePointJetBounded m (fun n => (S.transitionData hepsilon n).phi)
      (fun _ => 0) atTop := by
  let T := S.transitionData hepsilon
  let A := fun n => (S.input n).recentCenteredField (S.point n)
    (-(S.input n).recent_duration)
  let C := fun n => (S.input n).olderCenteredField (S.point n) 0
  let r := fun n => (S.input n).older_neck.neck.scale ^ 2
  have hCs (n : ℕ) : ContDiffAt ℝ ∞ (C n) 0 :=
    ((T n).older_fields 0).smooth.contDiffAt
      ((T n).target_open.mem_nhds (T n).target_center)
  have hA : PointJetsConverge A (fun _ => 0) (evolvingCylinderModelField (-d)) 0 atTop :=
    S.joining_pointJetsConverge hepsilon hlim S.point (S.recent_point_mem hepsilon)
  have hC : PointJetsConverge C (fun _ => 0) (evolvingCylinderModelField 0) 0 atTop :=
    S.older_zero_pointJetsConverge hepsilon
  have hr : Tendsto r atTop (𝓝 (1 + d)) := S.scale_sq_tendsto hepsilon hd.1 hlim
  have hscaled := hC.const_smul_family hr hCs
    (evolvingCylinderModelField_contDiff 0).contDiffAt
  have htarget (n : ℕ) : SmoothPositiveCoefficients
      (fun p => r n • C n p) (T n).target :=
    ((T n).older_fields 0).smul (sq_pos_of_pos (S.input n).older_neck.neck.scale_pos)
  have hH := S.older_error_pointJetsVanish hepsilon (fun _ => 0) (fun _ => by norm_num)
  have hfirst := bounded_first_transition_derivative
    (S.joining_error_pointJetsVanish hepsilon) hH
    (fun n => ⟨neg_le_neg (S.recent_short n).le,
      neg_nonpos.mpr (S.input n).recent_duration_pos.le⟩)
    (fun n => (S.scale_gt_one n).le) (fun n => (T n).center)
    (fun n v w => ?_)
  · apply bounded_transition_jets_of_metric_convergence
      (fun n => (T n).source_open) (fun n => (T n).target_open)
      (fun n => (T n).source_center) (fun n => (T n).target_center)
      (fun n => ((T n).recent_fields _).smooth) (fun n => (htarget n).smooth)
      (fun n => ((T n).recent_fields _).invertible) (fun n => (htarget n).invertible)
      (fun n => (htarget n).symmetric) (fun n => (T n).smooth)
      (fun n => (T n).mapsTo) (fun n => (T n).center) (fun n p hp v w => ?_)
      hA hscaled (evolvingCylinderModelField_contDiff (-d)).contDiffAt
      ((evolvingCylinderModelField_contDiff 0).const_smul (1 + d)).contDiffAt
      (model_evolvingCylinderField_isInvertible (by linarith [hd.1]) 0)
      (model_evolvingCylinder_smul_isInvertible (by linarith [hd.1]) (by norm_num) 0)
      hfirst
    exact congrArg (fun B : MetricCoefficient 3 => B v w) ((T n).joining_metric p hp)
  · exact congrArg (fun B : MetricCoefficient 3 => B v w)
      ((T n).joining_metric 0 (T n).source_center)

end PoincareConjecture.M45
