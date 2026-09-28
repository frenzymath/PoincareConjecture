import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryForPotential
import Mathlib.Topology.ExtendFrom













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)








theorem annular_harmonic_fderiv_boundary_limit
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (x : closure scalarAnnulus) (hxnorm : ‖(x : Plane)‖ = 1 ∨ ‖(x : Plane)‖ = 2) :
    ∃ L : Plane →L[ℝ] ℝ, L ≠ 0 ∧
      Tendsto (fderiv ℝ H) (𝓝[scalarAnnulus] (x : Plane)) (𝓝 L) := by
  obtain ⟨e, O, J, hx, -, hO, -, -, hOs, he, hei, hflat, hshape,
    hJc, hJeq, -, hJne⟩ :=
    annular_harmonic_noncritical_boundary D hHc hHs hlap hinner houter x hxnorm
  obtain ⟨r, hr, hshape⟩ := hshape
  have hzs : e.symm (x : Plane) ∈ e.source := e.map_target hx
  have hes := contMDiffOn_iff_contDiffOn.mp he
  have heis := contMDiffOn_iff_contDiffOn.mp hei
  have heid := (heis.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)
  have hed := (hes.contDiffAt (e.open_source.mem_nhds hzs)).differentiableAt (by simp)
  have hinverse : (fderiv ℝ e.symm (x : Plane)).comp
      (fderiv ℝ e (e.symm (x : Plane))) = ContinuousLinearMap.id ℝ Plane := by
    have heid' : DifferentiableAt ℝ e.symm (e (e.symm (x : Plane))) := by
      simpa only [e.right_inv hx] using heid
    have hcomp := fderiv_comp (e.symm (x : Plane)) heid' hed
    rw [e.right_inv hx] at hcomp
    rw [← hcomp]
    have hloc : (e.symm : Plane → Plane) ∘ e =ᶠ[𝓝 (e.symm (x : Plane))] id := by
      filter_upwards [e.open_source.mem_nhds hzs] with z hz
      exact e.left_inv hz
    simpa only [fderiv_id] using hloc.fderiv_eq (𝕜 := ℝ)
  let E : Plane → Plane →L[ℝ] ℝ := fun y => (J (e.symm y)).comp (fderiv ℝ e.symm y)
  have hEc : ContinuousAt E (x : Plane) :=
    ((hJc.continuousAt (e.open_source.mem_nhds hzs)).comp heid.continuousAt).clm_comp
      ((heis.continuousOn_fderiv_of_isOpen e.open_target (by simp)).continuousAt
        (e.open_target.mem_nhds hx))
  have hEne : E x ≠ 0 := by
    intro hzero
    apply hJne
    ext v
    have hv := congrArg (fun A : Plane →L[ℝ] ℝ => A (fderiv ℝ e (e.symm x) v)) hzero
    have hi := congrArg (fun A : Plane →L[ℝ] Plane => A v) hinverse
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
    simpa only [E, ContinuousLinearMap.comp_apply, hi, zero_apply] using hv
  have hball : ∀ᶠ y in 𝓝 (x : Plane), e.symm y ∈ Metric.ball (e.symm (x : Plane)) r :=
    heid.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have heq : fderiv ℝ H =ᶠ[𝓝[scalarAnnulus] (x : Plane)] E := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds hx),
      mem_nhdsWithin_of_mem_nhds hball] with y hy hyt hyball
    have hyO : e.symm y ∈ O := by
      rw [hshape]
      refine ⟨hyball, ?_⟩
      exact (hflat _ (e.map_target hyt)).mp (by simpa only [e.right_inv hyt] using hy)
    have hyd := ((contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds hy)).differentiableAt (by simp)
    have heyd := (hes.contDiffAt (e.open_source.mem_nhds
      (e.map_target hyt))).differentiableAt (by simp)
    have heiyd := (heis.contDiffAt (e.open_target.mem_nhds hyt)).differentiableAt (by simp)
    have hyd' : DifferentiableAt ℝ H (e (e.symm y)) := by
      simpa only [e.right_inv hyt] using hyd
    have hHed : DifferentiableAt ℝ (H ∘ e) (e.symm y) :=
      hyd'.comp _ heyd
    have hloc : (H ∘ e) ∘ e.symm =ᶠ[𝓝 y] H := by
      filter_upwards [e.open_target.mem_nhds hyt] with z hz
      simp only [Function.comp_apply, e.right_inv hz]
    calc
      fderiv ℝ H y = fderiv ℝ ((H ∘ e) ∘ e.symm) y := hloc.fderiv_eq.symm
      _ = (fderiv ℝ (H ∘ e) (e.symm y)).comp (fderiv ℝ e.symm y) :=
        fderiv_comp y hHed heiyd
      _ = E y := by rw [hJeq hyO]
  exact ⟨E x, hEne, hEc.continuousWithinAt.tendsto.congr' heq.symm⟩

end PoincareConjecture.M64Uniformization
