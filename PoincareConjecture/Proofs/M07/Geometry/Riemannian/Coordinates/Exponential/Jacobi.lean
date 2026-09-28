import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Equation
import PoincareConjecture.Proofs.M07.Analysis.Calculus.MixedDerivatives

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem geodesicVariation_jacobi_retained
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ S)
    (Γ : GeodesicVariation g.euclideanCoefficients S I) :
    ∀ t ∈ I,
      alongCovariantDerivative g.euclideanCoefficients
          (fun τ => (Γ.phase (0, τ)).1)
          (alongCovariantDerivative g.euclideanCoefficients
            (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t +
        coordinateCurvature g.euclideanCoefficients (Γ.phase (0, t)).1
          (variationField Γ t) (Γ.phase (0, t)).2 (Γ.phase (0, t)).2 = 0 := by
  exact geodesicVariation_jacobi (B := g.euclideanCoefficients)
    (U := Set.univ) isOpen_univ
    ((contDiff_iff_contDiffAt.mpr (fun x => g.contDiffAt_euclideanCoefficients x)).contDiffOn)
    (fun x _ => g.inner_isInvertible x) (fun x _ u v => g.symm x u v)
    hS hI h0 Γ (fun _ _ _ _ => mem_univ _)

theorem geodesicVariation_jacobi_curvature
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ S)
    (Γ : GeodesicVariation g.euclideanCoefficients S I) :
    ∀ t ∈ I,
      alongCovariantDerivative g.euclideanCoefficients
          (fun τ => (Γ.phase (0, τ)).1)
          (alongCovariantDerivative g.euclideanCoefficients
            (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t =
        -(D.curvature (Γ.phase (0, t)).1
          (variationField (E := EuclideanSpace ℝ (Fin n)) Γ t)
          (Γ.phase (0, t)).2 (Γ.phase (0, t)).2 :
            EuclideanSpace ℝ (Fin n)) := by
  intro t ht
  rw [← coordinateCurvature_eq_retained D]
  exact eq_neg_of_add_eq_zero_left (geodesicVariation_jacobi_retained D hS hI h0 Γ t ht)

def radialVariation {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) (v w : E) : ℝ × ℝ → E :=
  fun p => (D.trajectory (v + p.1 • w) p.2).1

theorem radialVariation_initial
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) {v w : E}
    (hdom : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, v + s • w ∈ D.domain) :
    radialVariation D v w (0, 0) = x := by
  simpa [radialVariation] using congrArg Prod.fst
    (D.trajectory_initial (hdom 0 ⟨by norm_num, by norm_num⟩))

theorem radialVariation_field_initial
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) {v w : E}
    (hdom : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, v + s • w ∈ D.domain) :
    fderiv ℝ (fun s => radialVariation D v w (s, 0)) 0 1 = 0 := by
  have heq : (fun s => radialVariation D v w (s, 0)) =ᶠ[𝓝 0] fun _ => x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with s hs
    exact congrArg Prod.fst (D.trajectory_initial (hdom s hs))
  simp [heq.fderiv_eq]

theorem radialVariation_field_initial_time_deriv
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) {v w : E}
    (hdom : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, v + s • w ∈ D.domain) :
    fderiv ℝ (fun t => fderiv ℝ (fun s => radialVariation D v w (s, t)) 0 1) 0 1 = w := by
  have hv : v ∈ D.domain := by simpa using hdom 0 ⟨by norm_num, by norm_num⟩
  have ht : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hsmooth : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ => radialVariation D v w (p.2, p.1)) (0, 0) := by
    have hphase : (v, (0 : ℝ)) ∈ D.domain ×ˢ Ioo (-2 : ℝ) 2 := ⟨hv, ht⟩
    have hout := D.smooth_trajectory.contDiffAt
      ((D.isOpen_domain.prod (isOpen_Ioo : IsOpen (Ioo (-2 : ℝ) 2))).mem_nhds hphase)
    have hout0 : ContDiffAt ℝ ∞ (fun z : E × ℝ => D.trajectory z.1 z.2)
        (v + (0 : ℝ) • w, (0 : ℝ)) := by simpa using hout
    have hin : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (v + p.2 • w, p.1)) (0, 0) :=
      (contDiffAt_const.add (contDiffAt_snd.smul contDiffAt_const)).prodMk contDiffAt_fst
    simpa only [radialVariation, Function.comp_def] using (hout0.comp (0, 0) hin).fst
  have htime : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt
      (fun t => radialVariation D v w (s, t)) (v + s • w) 0 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with s hs
    have hproj := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0
      (D.trajectory_hasDerivAt (hdom s hs) ht)
    have hinit := congrArg Prod.snd (D.trajectory_initial (hdom s hs))
    change HasDerivAt (fun t => (D.trajectory (v + s • w) t).1)
      ((D.trajectory (v + s • w) 0).2) 0 at hproj
    rw [hinit] at hproj
    simpa [radialVariation, Function.comp_def] using hproj
  have hmixed := Poincare.Analysis.hasDerivAt_fderiv_time_of_eventually hsmooth htime (1 : ℝ)
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  rw [fderiv_eq_smul_deriv, one_smul]
  exact hmixed.deriv.trans (by rw [fderiv_eq_smul_deriv, one_smul, hline.deriv])

theorem radialVariation_endpoint
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) {v w : E}
    (_hdom : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, v + s • w ∈ D.domain) :
    (fun s => radialVariation D v w (s, 1)) 0 = D.exponential v := by
  simpa [radialVariation] using D.trajectory_endpoint v

theorem radialVariation_endpoint_deriv
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
    (D : LocalFlowData B U x) {v w : E}
    (hdom : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, v + s • w ∈ D.domain) :
    fderiv ℝ (fun s => radialVariation D v w (s, 1)) 0 1 =
      fderiv ℝ D.exponential v w := by
  have hv : v ∈ D.domain := by
    simpa using hdom 0 ⟨by norm_num, by norm_num⟩
  have hd := (D.smooth_exponential.contDiffAt
    (D.isOpen_domain.mem_nhds hv)).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => D.exponential (v + s • w))
      (fderiv ℝ D.exponential v w) 0 := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
        (((hasDerivAt_id 0).smul_const w).const_add v) (by simp)
  simpa only [radialVariation, D.trajectory_endpoint, fderiv_apply_one_eq_deriv] using hline.deriv

end PoincareConjecture.CoordinateExponential
