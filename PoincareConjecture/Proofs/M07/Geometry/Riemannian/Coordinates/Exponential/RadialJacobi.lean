import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential.LocalFlowData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
variable (D : LocalFlowData B U x)

def radialParameterDomain (v w : E) : Set ℝ :=
  {s | v + s • w ∈ D.domain}

theorem isOpen_radialParameterDomain (v w : E) :
    IsOpen (D.radialParameterDomain v w) :=
  D.isOpen_domain.preimage (by fun_prop)

theorem zero_mem_radialParameterDomain {v : E} (hv : v ∈ D.domain) (w : E) :
    (0 : ℝ) ∈ D.radialParameterDomain v w := by
  simpa [radialParameterDomain] using hv


def radialGeodesicVariation {v : E} (hv : v ∈ D.domain) (w : E) :
    GeodesicVariation B (D.radialParameterDomain v w) (Ioo (-2 : ℝ) 2) where
  phase p := D.trajectory (v + p.1 • w) p.2
  smooth := D.smooth_trajectory.comp
    ((contDiffOn_const.add (contDiffOn_fst.smul contDiffOn_const)).prodMk contDiffOn_snd)
    (fun _ hp => hp)
  base_mem := D.zero_mem_radialParameterDomain hv w
  geodesic := fun _ hs _ ht => D.trajectory_hasDerivAt hs ht

theorem radialGeodesicVariation_stays {v : E} (hv : v ∈ D.domain) (w : E)
    {s t : ℝ} (hs : s ∈ D.radialParameterDomain v w) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    ((D.radialGeodesicVariation hv w).phase (s, t)).1 ∈ U :=
  D.trajectory_mem hs ht


theorem radialGeodesicVariation_jacobi [CompleteSpace E]
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u)
    {v : E} (hv : v ∈ D.domain) (w : E) :
    ∀ t ∈ Ioo (-2 : ℝ) 2,
      alongCovariantDerivative B (fun τ => (D.trajectory v τ).1)
          (alongCovariantDerivative B (fun τ => (D.trajectory v τ).1)
            (variationField (D.radialGeodesicVariation hv w)) ·) t +
        coordinateCurvature B (D.trajectory v t).1
          (variationField (D.radialGeodesicVariation hv w) t)
          (D.trajectory v t).2 (D.trajectory v t).2 = 0 := by
  simpa only [radialGeodesicVariation, zero_smul, add_zero] using
    geodesicVariation_jacobi hU hB hinv hsymm
      (D.isOpen_radialParameterDomain v w) isOpen_Ioo
      (D.zero_mem_radialParameterDomain hv w) (D.radialGeodesicVariation hv w)
      (fun _ hs _ ht => D.radialGeodesicVariation_stays hv w hs ht)

theorem radialGeodesicVariation_smooth_field {v : E} (hv : v ∈ D.domain) (w : E) :
    ContDiffOn ℝ ∞ (variationField (D.radialGeodesicVariation hv w)) (Ioo (-2 : ℝ) 2) := by
  let q : ℝ × ℝ → E := fun p => (D.trajectory (v + p.1 • w) p.2).1
  have hq {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : ContDiffAt ℝ ∞ q (0, t) :=
    ((D.radialGeodesicVariation hv w).smooth.contDiffAt
      (((D.isOpen_radialParameterDomain v w).prod isOpen_Ioo).mem_nhds
        ⟨D.zero_mem_radialParameterDomain hv w, ht⟩)).fst
  intro t ht
  have hd : ContDiffAt ℝ ∞ (fun r : ℝ => fderiv ℝ q (0, r) (1, 0)) t :=
    ((hq ht).fderiv_right (m := ∞) (by simp) |>.comp t
      (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  apply (hd.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  have hc : HasDerivAt (fun s : ℝ => (s, r)) (1, 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (x := 0) r)
  have hs := ((hq hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  simpa [Function.comp_def, variationField, radialGeodesicVariation, q] using hs.deriv

theorem radialGeodesicVariation_initial {v : E} (hv : v ∈ D.domain) (w : E) :
    variationField (D.radialGeodesicVariation hv w) 0 = 0 := by
  have heq : (fun s => (D.trajectory (v + s • w) 0).1) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => x) := by
    filter_upwards [(D.isOpen_radialParameterDomain v w).mem_nhds
      (D.zero_mem_radialParameterDomain hv w)] with s hs
    exact congrArg Prod.fst (D.trajectory_initial hs)
  change fderiv ℝ (fun s => (D.trajectory (v + s • w) 0).1) 0 1 = 0
  rw [heq.fderiv_eq]
  simp

theorem radialGeodesicVariation_initial_deriv {v : E} (hv : v ∈ D.domain) (w : E) :
    fderiv ℝ (variationField (D.radialGeodesicVariation hv w)) 0 1 = w := by
  have hzero : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
  have hsmooth : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ => (D.trajectory (v + p.2 • w) p.1).1) (0, 0) := by
    have h : ContDiffAt ℝ ∞
        (fun p : ℝ × ℝ => (D.trajectory (v + p.1 • w) p.2).1) (0, 0) :=
      ((D.radialGeodesicVariation hv w).smooth.contDiffAt
      (((D.isOpen_radialParameterDomain v w).prod isOpen_Ioo).mem_nhds
        ⟨D.zero_mem_radialParameterDomain hv w, hzero⟩)).fst
    exact ContDiffAt.comp (f := fun p : ℝ × ℝ => (p.2, p.1))
      (g := fun p : ℝ × ℝ => (D.trajectory (v + p.1 • w) p.2).1)
      (0, 0) h (contDiffAt_snd.prodMk contDiffAt_fst)
  have htime : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt
      (fun t => (D.trajectory (v + s • w) t).1) (v + s • w) 0 := by
    filter_upwards [(D.isOpen_radialParameterDomain v w).mem_nhds
      (D.zero_mem_radialParameterDomain hv w)] with s hs
    have h := (D.trajectory_hasDerivAt hs hzero).fst
    have hinit := congrArg Prod.snd (D.trajectory_initial hs)
    change HasDerivAt (fun t => (D.trajectory (v + s • w) t).1)
      (D.trajectory (v + s • w) 0).2 0 at h
    rwa [hinit] at h
  have hmixed := Poincare.Analysis.hasDerivAt_fderiv_time_of_eventually
    hsmooth htime (1 : ℝ)
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  change fderiv ℝ (fun t => fderiv ℝ
    (fun s => (D.trajectory (v + s • w) t).1) 0 1) 0 1 = w
  rw [fderiv_eq_smul_deriv, one_smul]
  exact hmixed.deriv.trans (by rw [fderiv_eq_smul_deriv, one_smul, hline.deriv])

theorem radialGeodesicVariation_initial_covariantDerivative
    {v : E} (hv : v ∈ D.domain) (w : E) :
    alongCovariantDerivative B (fun t => (D.trajectory v t).1)
      (variationField (D.radialGeodesicVariation hv w)) 0 = w := by
  rw [alongCovariantDerivative, D.radialGeodesicVariation_initial_deriv hv w,
    D.radialGeodesicVariation_initial hv w]
  simp [coordinateChristoffel, metricKoszulCovector]

theorem radialGeodesicVariation_endpoint {v : E} (hv : v ∈ D.domain) (w : E) :
    variationField (D.radialGeodesicVariation hv w) 1 =
      fderiv ℝ D.exponential v w := by
  have hcurve : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hd := (D.smooth_exponential.contDiffAt
    (D.isOpen_domain.mem_nhds hv)).differentiableAt (by simp)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  change fderiv ℝ (fun s => (D.trajectory (v + s • w) 1).1) 0 1 = _
  simp_rw [D.trajectory_endpoint]
  rw [fderiv_eq_smul_deriv, one_smul]
  exact hcomp.deriv

end PoincareConjecture.CoordinateExponential.LocalFlowData
