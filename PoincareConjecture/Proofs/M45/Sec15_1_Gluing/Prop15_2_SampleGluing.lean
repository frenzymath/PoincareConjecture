import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_TransitionSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance sampleGluingCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance sampleGluingCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

variable {epsilon : ℝ} (S : GluingBadSequence.{u} epsilon)

theorem GluingBadSequence.identified_error_pointJetsVanish (hepsilon : 0 < epsilon)
    {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d)) :
    PointJetsVanish (fun n p =>
      (S.input n).identifiedCenteredField (S.point n) (S.time n) p -
        evolvingCylinderModelField (S.time n) p) (fun _ => 0) atTop := by
  let T := S.transitionData hepsilon
  let A := fun n => (S.input n).recentCenteredField (S.point n)
    (-(S.input n).recent_duration)
  let C := fun n => (S.input n).olderCenteredField (S.point n) 0
  let D := fun n => (S.input n).olderCenteredField (S.point n) (S.normalizedOlderTime n)
  let r := fun n => (S.input n).older_neck.neck.scale ^ 2
  let s := fun n => -(S.input n).recent_duration
  have hAs (n : ℕ) : ContDiffAt ℝ ∞ (A n) 0 :=
    ((T n).recent_fields _).smooth.contDiffAt
      ((T n).source_open.mem_nhds (T n).source_center)
  have hCs (n : ℕ) : ContDiffAt ℝ ∞ (C n) 0 :=
    ((T n).older_fields 0).smooth.contDiffAt
      ((T n).target_open.mem_nhds (T n).target_center)
  have hDs (n : ℕ) : ContDiffAt ℝ ∞ (D n) 0 :=
    ((T n).older_fields _).smooth.contDiffAt
      ((T n).target_open.mem_nhds (T n).target_center)
  have hphi (n : ℕ) : ContDiffAt ℝ ∞ (T n).phi 0 :=
    (T n).smooth.contDiffAt ((T n).source_open.mem_nhds (T n).source_center)
  have hA : PointJetsConverge A (fun _ => 0) (evolvingCylinderModelField (-d)) 0 atTop :=
    S.joining_pointJetsConverge hepsilon hlim S.point (S.recent_point_mem hepsilon)
  have hC : PointJetsConverge C (fun _ => 0) (evolvingCylinderModelField 0) 0 atTop :=
    S.older_zero_pointJetsConverge hepsilon
  have hH := S.older_error_pointJetsVanish hepsilon (fun _ => 0) (fun _ => by norm_num)
  have hr : atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖r n‖) :=
    (S.scale_sq_tendsto hepsilon hd.1 hlim).norm.isBoundedUnder_le
  have hts : atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖S.time n - s n‖) := by
    refine ⟨2, ?_⟩
    change ∀ᶠ n in atTop, ‖S.time n - s n‖ ≤ 2
    apply Eventually.of_forall
    intro n
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    dsimp only [s]
    constructor <;> linarith [(S.time_mem n).1, (S.time_mem n).2,
      (S.input n).recent_duration_pos, S.recent_short n]
  have herror := affine_neck_gluing_error_vanish
    (A := A) (C := C) (D := D) (phi := fun n => (T n).phi)
    (r := r) (s := s) (t := S.time) (tau := S.normalizedOlderTime)
    (by linarith [hd.1] : -d < 1) hAs hCs hDs hphi (fun n => (T n).center)
    (fun n => ((T n).recent_fields _).invertible 0 (T n).source_center)
    (fun n => ((T n).older_fields 0).invertible 0 (T n).target_center)
    hA hC (S.joining_error_pointJetsVanish hepsilon) hH
    (S.older_error_pointJetsVanish hepsilon S.normalizedOlderTime S.normalizedOlderTime_mem)
    (S.transition_jets_bounded hepsilon hd hlim) hr hts (fun n => ?_)
    (fun n => eventually_of_mem ((T n).source_open.mem_nhds (T n).source_center)
      (T n).joining_metric) (fun n => (T n).joining_ricci)
  · apply herror.congr
    intro n
    have he := (T n).older_metric (S.normalizedOlderTime n)
    rw [S.normalizedOlderTime_eq n] at he
    filter_upwards [he] with p hp
    exact congrArg (fun B : MetricCoefficient 3 => B - evolvingCylinderModelField (S.time n) p)
      hp.symm
  · have ht := S.normalizedOlderTime_eq n
    dsimp only [r, s]
    nlinarith only [ht]

theorem GluingBadSequence.piecewise_error_pointJetsVanish (hepsilon : 0 < epsilon)
    {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d)) :
    PointJetsVanish (fun n p => centeredCylinderMetric
      ((S.input n).piecewiseTensor (S.input n).recent_patch.coordinate (S.time n))
      (S.point n).1 (S.point n).2 p - evolvingCylinderModelField (S.time n) p)
      (fun _ => 0) atTop := by
  apply (S.identified_error_pointJetsVanish hepsilon hd hlim).congr
  intro n
  apply Eventually.of_forall
  intro p
  simp only [M45NeckGluingInput.piecewiseTensor, if_neg (not_le.mpr (S.time_older n)),
    M45NeckGluingInput.identifiedCenteredField]

end PoincareConjecture.M45
