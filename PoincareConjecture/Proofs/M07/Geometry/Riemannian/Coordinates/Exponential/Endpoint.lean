import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Flow

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.CoordinateExponential.LocalFlowData

open Set Metric Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
variable (D : LocalFlowData B U x)

def time : ℝ := D.radius / 2

theorem time_pos : 0 < D.time := half_pos D.radius_pos

theorem time_mem : D.time ∈ Ioo (-D.radius) D.radius := by
  dsimp [time]
  constructor <;> linarith [D.radius_pos]

def endpoint (v : E) : E := (D.flow (v, D.time)).1

theorem smooth_endpoint : ContDiffOn ℝ ∞ D.endpoint (ball 0 D.radius) :=
  D.smooth.fst.comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hv => ⟨hv, D.time_mem⟩)

theorem endpoint_zero : D.endpoint 0 = x :=
  congrArg Prod.fst (D.zero D.time_mem)

theorem hasDerivAt_endpoint_smul {v : E} (hv : v ∈ ball 0 D.radius) :
    HasDerivAt (fun s : ℝ => D.endpoint (s • v)) (D.time • v) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-D.radius) D.radius :=
    ⟨by linarith [D.radius_pos], D.radius_pos⟩
  have hcurve : HasDerivAt (fun s => (D.flow (v, s)).1) v 0 := by
    simpa [D.initial v hv, coordinateGeodesicField, Function.comp_def] using
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0
        (D.hasDerivAt v hv 0 hzero)
  have htime : HasDerivAt (fun s : ℝ => (D.flow (v, s * D.time)).1) (D.time • v) 0 := by
    simpa only [Function.comp_def, one_mul, id_eq] using
      hcurve.scomp_of_eq 0 ((hasDerivAt_id 0).mul_const D.time) (by simp)
  apply htime.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
    with s hs
  simpa only [endpoint, velocityScale_fst] using
    congrArg Prod.fst (D.scaling (abs_lt.mpr hs).le hv D.time_mem)

theorem hasFDerivAt_endpoint_zero :
    HasFDerivAt D.endpoint (D.time • ContinuousLinearMap.id ℝ E) 0 := by
  have hd := (D.smooth_endpoint.contDiffAt (ball_mem_nhds 0 D.radius_pos)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hlinear : (fun v => fderiv ℝ D.endpoint 0 v) =ᶠ[𝓝 (0 : E)]
      (fun v => D.time • v) := by
    filter_upwards [ball_mem_nhds (0 : E) D.radius_pos] with v hv
    have hline : HasDerivAt (fun s : ℝ => D.endpoint (s • v))
        (fderiv ℝ D.endpoint 0 v) 0 := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
          ((hasDerivAt_id 0).smul_const v) (by simp)
    exact hline.unique (D.hasDerivAt_endpoint_smul hv)
  have hA : HasFDerivAt (fun v : E => D.time • v) (fderiv ℝ D.endpoint 0) 0 :=
    (fderiv ℝ D.endpoint 0).hasFDerivAt.congr_of_eventuallyEq hlinear.symm
  exact hd.hasFDerivAt.congr_fderiv
    (hA.unique ((hasFDerivAt_id (0 : E)).const_smul D.time))

def domain : Set E := (fun v : E => D.time⁻¹ • v) ⁻¹' ball 0 D.radius

theorem isOpen_domain : IsOpen D.domain := by
  change IsOpen ((fun v : E => D.time⁻¹ • v) ⁻¹' ball (0 : E) D.radius)
  exact isOpen_ball.preimage (by fun_prop)

theorem zero_mem_domain : (0 : E) ∈ D.domain := by
  simpa [domain] using (mem_ball_self D.radius_pos : (0 : E) ∈ ball 0 D.radius)

def exponential (v : E) : E := D.endpoint (D.time⁻¹ • v)

theorem exponential_zero : D.exponential 0 = x := by
  simpa [exponential] using D.endpoint_zero

theorem smooth_exponential : ContDiffOn ℝ ∞ D.exponential D.domain :=
  D.smooth_endpoint.comp ((contDiff_id.const_smul _).contDiffOn) (fun _ hv => hv)

theorem hasFDerivAt_exponential_zero :
    HasFDerivAt D.exponential (ContinuousLinearMap.id ℝ E) 0 := by
  have houter : HasFDerivAt D.endpoint (D.time • ContinuousLinearMap.id ℝ E)
      (D.time⁻¹ • (0 : E)) := by simpa using D.hasFDerivAt_endpoint_zero
  have h := houter.comp 0 ((hasFDerivAt_id (0 : E)).const_smul D.time⁻¹)
  apply h.congr_fderiv
  ext v
  simp [smul_smul, D.time_pos.ne']

def trajectory (v : E) (t : ℝ) : E × E :=
  velocityScale D.time (D.flow (D.time⁻¹ • v, D.time * t))

theorem trajectory_initial {v : E} (hv : v ∈ D.domain) :
    D.trajectory v 0 = (x, v) := by
  simp only [trajectory, mul_zero, D.initial _ hv]
  ext <;> simp [smul_smul, D.time_pos.ne']

theorem trajectory_endpoint (v : E) : (D.trajectory v 1).1 = D.exponential v := by
  simp only [trajectory, mul_one, velocityScale_fst, exponential, endpoint]

theorem normalized_time_mem {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    D.time * t ∈ Ioo (-D.radius) D.radius := by
  have hp := D.time_pos
  have hmullo := mul_lt_mul_of_pos_left ht.1 hp
  have hmulhi := mul_lt_mul_of_pos_left ht.2 hp
  dsimp [time] at *
  constructor <;> nlinarith

theorem smooth_trajectory :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => D.trajectory p.1 p.2)
      (D.domain ×ˢ Ioo (-2 : ℝ) 2) := by
  exact (velocityScale (E := E) D.time).contDiff.contDiffOn.comp
    (D.smooth.comp ((contDiffOn_fst.const_smul _).prodMk
      (contDiffOn_const.mul contDiffOn_snd))
      (fun p hp => ⟨hp.1, D.normalized_time_mem hp.2⟩)) (fun _ _ => mem_univ _)

theorem trajectory_hasDerivAt {v : E} (hv : v ∈ D.domain)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (D.trajectory v) (coordinateGeodesicField B (D.trajectory v t)) t := by
  exact hasDerivAt_velocityScale (D.hasDerivAt _ hv _ (D.normalized_time_mem ht))

theorem trajectory_mem {v : E} (hv : v ∈ D.domain)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : (D.trajectory v t).1 ∈ U := by
  exact (D.field_ball_subset (D.stays _ hv _ (D.normalized_time_mem ht))).1

end PoincareConjecture.CoordinateExponential.LocalFlowData
