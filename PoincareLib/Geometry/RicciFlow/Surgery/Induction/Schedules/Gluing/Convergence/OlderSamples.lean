import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Convergence.Countersequence
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Convergence.SequenceJets
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Support.ActualCoefficientFields
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.ModelJetConvergence

/-!
# Older normalized times and their improving error jets

Every violating physical time lies inside the older neck's full own
normalized interval. Both its joining and sampled coefficient fields
therefore carry vanishing finite errors at the actual old chart center.
Source: Proposition 15.2, pp. 353-354.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

open PoincareMT.MetricSurgery

namespace PoincareMT.M45

open M36 M44

variable {epsilon : ℝ} (S : GluingBadSequence.{u} epsilon)

/-- Every selected point lies in the actual improving recent cylinder.
Source: Proposition 15.2, pp. 353-354. -/
theorem GluingBadSequence.recent_point_mem (hepsilon : 0 < epsilon) (n : ℕ) :
    (S.point n).2 ∈ Ioo (-(S.beta n * epsilon)⁻¹) (S.beta n * epsilon)⁻¹ := by
  apply cylinderDomain_mono (mul_pos (S.beta_pos n) hepsilon) _ (S.point_mem n)
  nlinarith [S.beta_le_quarter n]

/-- The actual old image point remains strictly inside its own neck,
although its distance from the boundary need not be uniform.
Source: Proposition 15.2, pp. 353-354. -/
theorem GluingBadSequence.older_point_mem (hepsilon : 0 < epsilon) (n : ℕ) :
    ((S.input n).olderCenteredCoordinate (S.point n)).2 ∈
      Ioo (-(S.beta n * epsilon / 2)⁻¹) (S.beta n * epsilon / 2)⁻¹ := by
  let I := S.input n
  have hp : I.recent_patch.coordinate (S.point n) ∈ I.recent_patch.carrier := by
    rw [← I.recent_patch.coordinate_image]
    exact mem_image_of_mem _ ⟨mem_univ _, S.recent_point_mem hepsilon n⟩
  have ho : I.identify (I.recent_patch.coordinate (S.point n)) ∈ I.older_neck.neck.carrier :=
    I.identify_image (mem_image_of_mem I.identify hp)
  have h := (I.older_neck.neck.coordinate_inverse_mem _ ho).2
  simpa only [I.older_neck.epsilon_eq, M45NeckGluingInput.olderCenteredCoordinate, I] using h

/-- The selected physical time expressed in the older neck's own scale.
Source: Proposition 15.2, pp. 353-354. -/
noncomputable def GluingBadSequence.normalizedOlderTime (n : ℕ) : ℝ :=
  (S.time n + (S.input n).recent_duration) / (S.input n).older_neck.neck.scale ^ 2

/-- The actual bad sample is inside the complete older normalized window.
Source: Proposition 15.2, pp. 353-354. -/
theorem GluingBadSequence.normalizedOlderTime_mem (n : ℕ) :
    S.normalizedOlderTime n ∈ Ioc (-1 : ℝ) 0 := by
  have hr : 0 < (S.input n).older_neck.neck.scale ^ 2 := by
    linarith [S.scale_gt_one n]
  constructor
  · apply (lt_div_iff₀ hr).mpr
    nlinarith [(S.time_mem n).1, S.scale_gt_one n, (S.input n).recent_duration_pos]
  · apply div_nonpos_of_nonpos_of_nonneg _ hr.le
    linarith [S.time_older n]

/-- Normalizing and returning to physical time gives the exact sample time.
Source: Proposition 15.2, pp. 353-354. -/
theorem GluingBadSequence.normalizedOlderTime_eq (n : ℕ) :
    -(S.input n).recent_duration + S.normalizedOlderTime n *
      (S.input n).older_neck.neck.scale ^ 2 = S.time n := by
  have hr : (S.input n).older_neck.neck.scale ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (S.input n).older_neck.neck.scale_pos)
  dsimp only [GluingBadSequence.normalizedOlderTime]
  rw [div_mul_cancel₀ _ hr]
  ring

/-- Every choice of old normalized times in the complete interval has
vanishing actual centered error jets along the improving sequence.
Source: Proposition 15.2, pp. 353-354; GluingCompactness.md. -/
theorem GluingBadSequence.older_error_pointJetsVanish (hepsilon : 0 < epsilon)
    (tau : ℕ → ℝ) (htau : ∀ n, tau n ∈ Ioc (-1 : ℝ) 0) :
    PointJetsVanish (fun n p => (S.input n).olderCenteredField (S.point n) (tau n) p -
      evolvingCylinderModelField (tau n) p) (fun _ => 0) atTop := by
  have he (n : ℕ) : 0 < S.beta n * epsilon / 2 :=
    div_pos (mul_pos (S.beta_pos n) hepsilon) (by norm_num)
  have he0 : Tendsto (fun n => S.beta n * epsilon / 2) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_div] using
      (S.beta_tendsto_zero.mul_const epsilon).div_const (2 : ℝ)
  apply evolvingCylinderError_pointJetsVanish he he0 (fun n => ⟨(htau n).1.le, (htau n).2⟩)
    (fun n => ?_) (S.older_point_mem hepsilon)
  obtain ⟨hs, bound, hbound, hjets⟩ := (S.input n).older_neck.comparison
  exact ⟨hs _ (htau n), bound, hbound, hjets _ (htau n)⟩

/-- The actual older normalized joining coefficients converge to the
static cylinder at their actual centered point.
Source: Proposition 15.2, pp. 353-354; GluingCompactness.md. -/
theorem GluingBadSequence.older_zero_pointJetsConverge (hepsilon : 0 < epsilon) :
    PointJetsConverge (fun n => (S.input n).olderCenteredField (S.point n) 0)
      (fun _ => 0) (evolvingCylinderModelField 0) 0 atTop := by
  have herror := S.older_error_pointJetsVanish hepsilon (fun _ => 0)
    (fun _ => by norm_num)
  have hmodel : PointJetsConverge (fun _ : ℕ => evolvingCylinderModelField 0)
      (fun _ => 0) (evolvingCylinderModelField 0) 0 atTop := fun _ => tendsto_const_nhds
  apply hmodel.of_sub_vanish herror (fun n => ?_)
    (fun _ => (evolvingCylinderModelField_contDiff 0).contDiffAt)
  apply ((S.input n).olderCenteredField_data (S.point n) 0).smooth.contDiffAt
  apply (centeredNeckDomain_isOpen _ _).mem_nhds
  apply zero_mem_centeredNeckDomain
  simpa only [(S.input n).older_neck.epsilon_eq] using S.older_point_mem hepsilon n

end PoincareMT.M45
