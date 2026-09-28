import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.ActualCoefficientFields
import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.NativeRicciNaturality
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.Hessian

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45NeckGluingInput

open M36 M45 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)

structure ActualTransitionData (hpos : 0 < beta * epsilon)
    (hsmall : beta * epsilon < 1 / 2) (z : RoundCylinderSpace) where
  phi : E → E
  source : Set E
  target : Set E
  source_open : IsOpen source
  target_open : IsOpen target
  source_center : (0 : E) ∈ source
  target_center : (0 : E) ∈ target
  source_subset : source ⊆ centeredNeckDomain (I.recentNeck hpos hsmall) z.2
  target_subset : target ⊆
    centeredNeckDomain I.older_neck.neck (I.olderCenteredCoordinate z).2
  smooth : ContDiffOn ℝ ∞ phi source
  mapsTo : MapsTo phi source target
  center : phi 0 = 0
  derivative_invertible : ∀ x ∈ source, (fderiv ℝ phi x).IsInvertible
  recent_fields : ∀ t, SmoothPositiveCoefficients (I.recentCenteredField z t) source
  older_fields : ∀ tau, SmoothPositiveCoefficients (I.olderCenteredField z tau) target
  joining_metric : ∀ x ∈ source, I.recentCenteredField z (-I.recent_duration) x =
    I.older_neck.neck.scale ^ 2 • neckCoefficientPullback phi (I.olderCenteredField z 0) x
  older_metric : ∀ tau,
    I.identifiedCenteredField z (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2) =ᶠ[𝓝 0]
      fun x => I.older_neck.neck.scale ^ 2 • neckCoefficientPullback phi
        (I.olderCenteredField z tau) x
  joining_ricci : (fun x => jetRicciBilinear
      (metricTwoJet (I.recentCenteredField z (-I.recent_duration)) x)) =ᶠ[𝓝 0]
    neckCoefficientPullback phi
      (fun x => jetRicciBilinear (metricTwoJet (I.olderCenteredField z 0) x))

theorem exists_actualTransitionData (hpos : 0 < beta * epsilon)
    (hsmall : beta * epsilon < 1 / 2) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹) :
    Nonempty (I.ActualTransitionData hpos hsmall z) := by
  obtain ⟨phi, U, hU, h0, hsub, hphi, hmap, hphi0, _hi0, hcoord⟩ :=
    I.exists_joining_centered_transition hpos hsmall z hz
  let V := centeredNeckDomain I.older_neck.neck (I.olderCenteredCoordinate z).2
  have hV : IsOpen V := centeredNeckDomain_isOpen _ _
  have h0V : (0 : E) ∈ V := by simpa only [hphi0] using hmap h0
  have hA (t : ℝ) : SmoothPositiveCoefficients (I.recentCenteredField z t) U := by
    have hfull := I.recentCenteredField_data hpos hsmall z t
    exact ⟨hfull.smooth.mono hsub, fun p hp => hfull.symmetric p (hsub hp),
      fun p hp => hfull.positive p (hsub hp), fun p hp => hfull.invertible p (hsub hp)⟩
  have hC (tau : ℝ) : SmoothPositiveCoefficients (I.olderCenteredField z tau) V :=
    I.olderCenteredField_data z tau
  have hscale : I.older_neck.neck.scale ^ 2 * I.older_neck.neck.scale⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ I.older_neck.neck.scale_pos.ne', one_pow]
  have hOlder (tau : ℝ) (p : E) (hp : p ∈ U) :
      I.identifiedCenteredField z
          (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2) p =
        I.older_neck.neck.scale ^ 2 • neckCoefficientPullback phi
          (I.olderCenteredField z tau) p := by
    let g := I.older_flow.metric (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2)
    have hmaps : I.olderCenteredMap z ∘ phi =ᶠ[𝓝 p] I.identify ∘ I.recentCenteredMap z :=
      eventually_of_mem (hU.mem_nhds hp) hcoord
    have hCs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (I.olderCenteredMap z) (phi p) :=
      centeredNeckLift_contMDiffAt I.older_neck.neck _ _ (hmap hp)
    have hcoeff : I.olderCenteredField z tau (phi p) =
        I.older_neck.neck.scale⁻¹ ^ 2 • g.pullbackCoefficients (I.olderCenteredMap z) (phi p) :=
      I.olderCenteredMap_normalizedCoefficients z tau (hmap hp)
    rw [I.identifiedCenteredField_eq hpos hsmall z _ (hsub hp),
      ← pullbackCoefficients_congr_of_eventuallyEq g hmaps,
      pullbackCoefficients_comp_bilinear g hCs (hphi.contDiffAt (hU.mem_nhds hp))]
    dsimp only [neckCoefficientPullback]
    rw [hcoeff]
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply, smul_apply, smul_eq_mul]
    rw [← mul_assoc, hscale, one_mul]
  have hmetric (p : E) (hp : p ∈ U) :
      I.recentCenteredField z (-I.recent_duration) p =
        I.older_neck.neck.scale ^ 2 • neckCoefficientPullback phi (I.olderCenteredField z 0) p := by
    have he : I.identifiedCenteredField z (-I.recent_duration) p =
        I.recentCenteredField z (-I.recent_duration) p := by
      rw [I.identifiedCenteredField_eq hpos hsmall z _ (hsub hp),
        I.joining_centered_coefficients hpos hsmall z (hsub hp)]
      exact I.recentCenteredMap_pullbackCoefficients hpos hsmall z _ (hsub hp)
    simpa only [zero_mul, add_zero, he] using hOlder 0 p hp
  have hinv (p : E) (hp : p ∈ U) : (fderiv ℝ phi p).IsInvertible := by
    have he (v w : E) : I.recentCenteredField z (-I.recent_duration) p v w =
        (I.older_neck.neck.scale ^ 2 • I.olderCenteredField z 0 (phi p))
          (fderiv ℝ phi p v) (fderiv ℝ phi p w) :=
      congrArg (fun B : MetricCoefficient 3 => B v w) (hmetric p hp)
    have hsur := CoordinateTransition.surjective_of_pullback_isInvertible
      ((hA (-I.recent_duration)).invertible p hp) he
    have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank ℝ E = Module.finrank ℝ E from rfl)).mpr hsur
    exact ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ phi p)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsur), rfl⟩
  refine ⟨{
    phi := phi
    source := U
    target := V
    source_open := hU
    target_open := hV
    source_center := h0
    target_center := h0V
    source_subset := hsub
    target_subset := subset_rfl
    smooth := hphi
    mapsTo := hmap
    center := hphi0
    derivative_invertible := hinv
    recent_fields := hA
    older_fields := hC
    joining_metric := hmetric
    older_metric := fun tau => eventually_of_mem (hU.mem_nhds h0) (hOlder tau)
    joining_ricci := ?_ }⟩
  filter_upwards [hU.mem_nhds h0] with p hp
  exact nativeRicci_local_homothety hU hV hp (hmap hp)
    (hA (-I.recent_duration)).smooth (hC 0).smooth
    (hA (-I.recent_duration)).symmetric (hA (-I.recent_duration)).positive
    (hC 0).symmetric (hC 0).positive (hphi.contDiffAt (hU.mem_nhds hp))
    (eventually_of_mem (hU.mem_nhds hp) hinv) (sq_pos_of_pos I.older_neck.neck.scale_pos)
    (eventually_of_mem (hU.mem_nhds hp) hmetric)

end PoincareConjecture.M45NeckGluingInput
