import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHeinzEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityRepresentative











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65StrictTrace





theorem continuous_boundary_parameter_lift
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] (gamma : LoopCircle → M)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) t ≠ 0)
    (beta : C(LoopCircle, LoopCircle)) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ (C : ℝ → M) (b : ℝ → ℝ) (R : ℝ),
      ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ C ∧ curveVelocity (n := 3) C 0 ≠ 0 ∧
      ContinuousAt b 0 ∧ b 0 = 0 ∧ 0 < R ∧
      ∀ t ∈ Icc (-R) R, C (b t) = gamma (beta (boundaryCirclePoint hp t)) := by
  let u := beta (boundaryCirclePoint hp 0)
  let puncture : LoopCircle := ⟨-(u : LoopPlane), by simp only [norm_neg, u.property]⟩
  have hcenter : puncturedArc puncture 0 = u := by
    apply Subtype.ext
    change Complex.orthonormalBasisOneI.repr
      (boundaryCoordinate (-Complex.orthonormalBasisOneI.repr.symm (-(u : LoopPlane))) 0) = u
    simp only [map_neg, neg_neg, boundaryCoordinate, mul_zero, Complex.exp_zero,
      mul_one, LinearIsometryEquiv.apply_symm_apply]
  let E := circleArgChart puncture
  have h0 : (0 : ℝ) ∈ E.target :=
    ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩
  have hu : u ∈ E.source := by
    have hh := E.map_target h0
    change puncturedArc puncture 0 ∈ E.source at hh
    rwa [hcenter] at hh
  have hEu : E u = 0 := by
    have hh := E.right_inv h0
    change E (puncturedArc puncture 0) = 0 at hh
    rwa [hcenter] at hh
  let b := fun t => E (beta (boundaryCirclePoint hp t))
  have hpoint : Continuous (boundaryCirclePoint hp) := by
    exact ((contDiff_diskBoundaryCoordinate p).continuous.comp
      (continuous_id.smul continuous_const)).subtype_mk _
  have hb : ContinuousAt b 0 := by
    have hpre : ContinuousAt (fun t => beta (boundaryCirclePoint hp t)) 0 :=
      (beta.continuous.comp hpoint).continuousAt
    have hpost : ContinuousAt E (beta (boundaryCirclePoint hp 0)) :=
      E.continuousOn.continuousAt (E.open_source.mem_nhds hu)
    exact ContinuousAt.comp (f := fun t => beta (boundaryCirclePoint hp t)) (x := 0) hpost hpre
  have hcap : ∀ᶠ t in 𝓝 (0 : ℝ), beta (boundaryCirclePoint hp t) ∈ E.source :=
    (beta.continuous.comp hpoint).continuousAt.eventually (E.open_source.mem_nhds hu)
  obtain ⟨r, hr, hrcap⟩ := Metric.mem_nhds_iff.mp hcap
  obtain ⟨hC, hC0⟩ := punctured_curve_regular gamma hsmooth hregular puncture
  refine ⟨gamma ∘ puncturedArc puncture, b, r / 2, hC, hC0, hb, hEu, by positivity, ?_⟩
  intro t ht
  have htball : t ∈ ball (0 : ℝ) r := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans_lt (half_lt_self hr)
  exact congrArg gamma (E.left_inv (hrcap htball))





theorem continuous_boundary_plane_geometry
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) {f q : LoopPlane → M} {R : ℝ} (hR : 0 < R)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hharm : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    (hconf : ∀ z ∈ ball (0 : LoopPlane) 1,
      ∃ a : ℝ, m60AreaGram g f z = a • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hq : ContinuousOn q (closedBall (0 : LoopPlane) R))
    {p : ℂ} (hp : ‖p‖ = 1)
    (heq : EqOn q (f ∘ diskBoundaryCoordinate p)
      (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})) :
    let c := chartAt LoopAmbient (q 0)
    let H := c ∘ q
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (r : ℝ),
      0 < r ∧ r ≤ R ∧ MapsTo q (closedBall (0 : LoopPlane) r) c.source ∧
      ContinuousOn H (closedBall (0 : LoopPlane) r) ∧
      ContDiffOn ℝ ∞ H (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      (∀ z ∈ ball (0 : LoopPlane) r ∩ {z | 0 < z 1},
        (∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
        ∑ i : Fin 2, M65Gauss.connectionCoefficient DE (H z)
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0) ∧
      ∀ z ∈ ball (0 : LoopPlane) r ∩ {z | 0 < z 1},
        gE.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
        gE.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ∧
        gE.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0 := by
  obtain ⟨gE, DE, r, hr, hrR, hsource, hHc, hHs, hmetric, hh⟩ :=
    continuous_boundary_harmonic_chart D hR hf hharm hq hp heq
  have hc := continuous_boundary_chart_conformal g gE hp hf hconf
    (heq.mono (inter_subset_inter_left _ (ball_subset_ball hrR))) hsource
      (fun z hz => (hmetric z hz).self_of_nhds)
  let H := (chartAt LoopAmbient (q 0)) ∘ q
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hzC (z : LoopPlane) (hz : z ∈ U) :
      Complex.orthonormalBasisOneI.repr.symm z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im} := by
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hz.1
    · change 0 < (Complex.orthonormalBasisOneI.repr.symm z).im
      simpa only [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, mul_one, zero_mul, add_zero, zero_add] using (show 0 < z 1 from hz.2)
  refine ⟨gE, DE, r, hr, hrR, hsource, hHc, hHs, ?_, ?_⟩
  · intro z hz
    have hcont := hHs.contDiffAt (hU.mem_nhds hz)
    have hcont' : ContDiffAt ℝ ∞ H
        (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm z)) := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hcont
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      plane_harmonic_of_complex_equation DE hcont' (hh _ (hzC z hz))
  · intro z hz
    obtain ⟨a, ha⟩ := hc _ (hzC z hz)
    have hdiff : DifferentiableAt ℝ H
        (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm z)) := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (hHs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hh := plane_conformal_of_complex_norm gE hdiff ha
    let x := Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm z)
    let v := fun w => fderiv ℝ H w (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    let w := fun y => fderiv ℝ H y (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    change gE.euclideanCoefficients (H x) (v x) (v x) =
        gE.euclideanCoefficients (H x) (w x) (w x) ∧
      gE.euclideanCoefficients (H x) (v x) (w x) = 0 at hh
    change gE.euclideanCoefficients (H z) (v z) (v z) =
        gE.euclideanCoefficients (H z) (w z) (w z) ∧
      gE.euclideanCoefficients (H z) (v z) (w z) = 0
    simpa only [x, LinearIsometryEquiv.apply_symm_apply] using hh

end PoincareConjecture.M65Boundary
