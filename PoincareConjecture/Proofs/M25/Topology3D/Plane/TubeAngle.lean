import PoincareConjecture.Proofs.M25.Topology3D.Plane.AngularCoordinate
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeCoordinates










set_option autoImplicit false

open Set Metric Function Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M25.Topology3D

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def curveTubeAngle (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) (p : (ℝ × ℝ) × E) : ℝ :=
  circleAngularCoordinate e (p.1.2, (curveTubeProjection q0 T (p.1.1, p.2) : E))



noncomputable def curveTubeAngularDomain (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) : Set ((ℝ × ℝ) × E) :=
  {p | (p.1.1, p.2) ∈ T.target ∧
    e.symm (curveTubeProjection q0 T (p.1.1, p.2) : E) *
      (Circle.exp (-p.1.2) : ℂ) ∈ Complex.slitPlane}



theorem sphereCircleParameter_curveTubeAngle (e : ℂ ≃ₗᵢ[ℝ] E)
    (q0 : sphere (0 : E) 1) (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (p : (ℝ × ℝ) × E) :
    sphereCircleParameter e (curveTubeAngle e q0 T p) =
      curveTubeProjection q0 T (p.1.1, p.2) :=
  sphereCircleParameter_circleAngularCoordinate e p.1.2 _



theorem curveTubeAngle_apply (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) (z a b : ℝ) (y : E)
    (hp : curveTubeProjection q0 T (z, y) = sphereCircleParameter e b)
    (hab : b - a ∈ Ioc (-Real.pi) Real.pi) :
    curveTubeAngle e q0 T ((z, a), y) = b := by
  unfold curveTubeAngle
  rw [hp]
  exact circleAngularCoordinate_sphereCircleParameter e a b hab



theorem mem_curveTubeAngularDomain_of_projection (e : ℂ ≃ₗᵢ[ℝ] E)
    (q0 : sphere (0 : E) 1) (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (z a b : ℝ) (y : E) (hy : (z, y) ∈ T.target)
    (hp : curveTubeProjection q0 T (z, y) = sphereCircleParameter e b)
    (hab : b - a ∈ Ioo (-Real.pi) Real.pi) :
    ((z, a), y) ∈ curveTubeAngularDomain e q0 T := by
  refine ⟨hy, ?_⟩
  change e.symm (curveTubeProjection q0 T (z, y) : E) * (Circle.exp (-a) : ℂ) ∈
    Complex.slitPlane
  rw [hp]
  exact sphereCircleParameter_mem_angularDomain e a b hab

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem curveTubeAngle_regular (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) {k : ℕ∞ω}
    (hInv : ContDiffOn ℝ k T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0) :
    IsOpen (curveTubeAngularDomain e q0 T) ∧
      ContDiffOn ℝ k (curveTubeAngle e q0 T) (curveTubeAngularDomain e q0 T) := by
  let H : Set ((ℝ × ℝ) × E) := {p | (p.1.1, p.2) ∈ T.target}
  let R : (ℝ × ℝ) × E → ℝ × E := fun p =>
    (p.1.2, (curveTubeProjection q0 T (p.1.1, p.2) : E))
  have hH : IsOpen H := T.open_target.preimage (continuous_fst.fst.prodMk continuous_snd)
  have hR : ∀ p ∈ H, ContDiffAt ℝ k R p := by
    intro p hp
    have hI := (hInv.contDiffAt (T.open_target.mem_nhds hp)).comp p
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hP := (contDiffAt_unitRadialProjection_coe q0 (hx _ hp)).comp p hI.snd
    exact contDiffAt_fst.snd.prodMk hP
  have hV : IsOpen (curveTubeAngularDomain e q0 T) := by
    change IsOpen (H ∩ R ⁻¹'
      {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane})
    exact (show ContinuousOn R H from fun p hp =>
      (hR p hp).continuousAt.continuousWithinAt).isOpen_inter_preimage hH
        (isOpen_circleAngularCoordinate_domain e)
  refine ⟨hV, ?_⟩
  intro p hp
  have hpR : R p ∈
      {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := hp.2
  have hA : ContDiffAt ℝ k (circleAngularCoordinate e) (R p) :=
    (contDiffOn_circleAngularCoordinate e (k := k)).contDiffAt
      ((isOpen_circleAngularCoordinate_domain e).mem_nhds hpR)
  exact (ContDiffAt.comp (g := circleAngularCoordinate e) (f := R) p hA
    (hR p hp.1)).contDiffWithinAt



theorem contDiffOn_fderiv_curveTubeAngle (e : ℂ ≃ₗᵢ[ℝ] E)
    (q0 : sphere (0 : E) 1) (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : (ℝ × ℝ) × E =>
      fderiv ℝ (fun y : E => curveTubeAngle e q0 T (p.1, y)) p.2)
        (curveTubeAngularDomain e q0 T) := by
  obtain ⟨hV, hA⟩ := curveTubeAngle_regular e q0 T hInv hx
  intro p hp
  have hcomp : ContDiffAt ℝ ∞
      (fun y : ((ℝ × ℝ) × E) × E => curveTubeAngle e q0 T (y.1.1, y.2))
      (p, p.2) :=
    ContDiffAt.comp (g := curveTubeAngle e q0 T)
      (f := fun y : ((ℝ × ℝ) × E) × E => (y.1.1, y.2)) (p, p.2)
      (hA.contDiffAt (hV.mem_nhds hp)) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (ContDiffAt.fderiv
    (f := fun p : (ℝ × ℝ) × E => fun y : E => curveTubeAngle e q0 T (p.1, y))
    (g := (Prod.snd : (ℝ × ℝ) × E → E)) hcomp contDiffAt_snd (by simp)).contDiffWithinAt



theorem fderiv_curveTubeAngle_apply_velocity (e : ℂ ≃ₗᵢ[ℝ] E)
    (q0 : sphere (0 : E) 1) (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    (gamma : ℝ → E) (z s : ℝ) (hc : DifferentiableAt ℝ gamma s)
    (hy : (z, gamma s) ∈ T.target)
    (hp : ∀ t : ℝ, curveTubeProjection q0 T (z, gamma t) = sphereCircleParameter e t) :
    fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (gamma s) (deriv gamma s) = 1 := by
  obtain ⟨hV, hA⟩ := curveTubeAngle_regular e q0 T hInv hx
  have hmem := mem_curveTubeAngularDomain_of_projection e q0 T z s s (gamma s) hy (hp s)
    (show s - s ∈ Ioo (-Real.pi) Real.pi by simp [Real.pi_pos])
  have hslice : DifferentiableAt ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y))
      (gamma s) :=
    ((hA.contDiffAt (hV.mem_nhds hmem)).comp (gamma s)
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have heq : ((fun y : E => curveTubeAngle e q0 T ((z, s), y)) ∘ gamma) =ᶠ[𝓝 s] id := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show s ∈ Ioo (s - Real.pi) (s + Real.pi) by constructor <;> linarith [Real.pi_pos])]
      with t ht
    exact curveTubeAngle_apply e q0 T z s t (gamma t) (hp t)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact (hslice.hasFDerivAt.comp_hasDerivAt s hc.hasDerivAt).unique
    ((hasDerivAt_id s).congr_of_eventuallyEq heq)

end InnerProduct

end PoincareConjecture.M25.Topology3D
