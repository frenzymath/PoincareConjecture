import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryChartLinearization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryTranslation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryEllipsoidRounding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.EllipsoidBoundaryImage
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereRegionChart











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Pointwise

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_boundary_disc_round_boundary (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        F '' ((fun w => (stereoInvFun hv w : E)) '' D.boundary) =
          (fun w => (stereoInvFun hv w : E)) '' sphere 0 r ∧
        (∀ x ∈ closedBall 0 1, F (stereoInvFun hv (D.chart x) : E) ≠ v) ∧
        ∃ C : Set E, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨A, r, hr, hr1, F₀, hF₀norm, hF₀track, C₀, hC₀, hF₀fix⟩ :=
    exists_boundary_disc_affine_image v hv D
  let S := (fun x => D.chart 0 + A (r • x)) '' closedBall 0 1
  have hS : IsCompact S := (isCompact_closedBall _ _).image (by fun_prop)
  obtain ⟨T, hTnorm, hTtrack, Cₜ, hCₜ, hCₜtarget, hTfix⟩ :=
    exists_boundary_translation v hv hS (-D.chart 0)
  have hTzero : T v = v := radialStereo_supported_fixes_pole v hv T hCₜtarget hTfix
  have hAcomp : IsCompact (A '' sphere 0 r) := (isCompact_sphere _ _).image A.continuous
  have hA0 : ∀ y ∈ A '' sphere 0 r, y ≠ 0 := by
    rintro y ⟨x, hx, rfl⟩
    exact A.map_ne_zero_iff.mpr
      (norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hx).trans_ne hr.ne'))
  obtain ⟨R, hRnorm, hRtrack, Cᵣ, hCᵣ, hCᵣtarget, hRfix⟩ :=
    exists_boundary_ellipsoid_rounding v hv A hAcomp hA0
  have hRzero : R v = v := radialStereo_supported_fixes_pole v hv R hCᵣtarget hRfix
  let F := (F₀.trans T).trans R
  have hscaled : (fun x => r • x) '' sphere (0 : (ℝ ∙ v)ᗮ) 1 = sphere 0 r := by
    change r • sphere (0 : (ℝ ∙ v)ᗮ) 1 = sphere 0 r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one] using
      smul_sphere' hr.ne' (0 : (ℝ ∙ v)ᗮ) 1
  have hAscaled : (fun x => A (r • x)) '' sphere 0 1 = A '' sphere 0 r := by
    rw [← image_image, hscaled]
  have htranslate (x : (ℝ ∙ v)ᗮ) (hx : x ∈ closedBall 0 1) :
      T (F₀ (stereoInvFun hv (D.chart x) : E)) = (stereoInvFun hv (A (r • x)) : E) := by
    rw [hF₀track x hx, hTtrack _ ⟨x, hx, rfl⟩]
    have hc : D.chart 0 + A (r • x) + -D.chart 0 = A (r • x) := by abel
    rw [hc]
  have hboundary (x : (ℝ ∙ v)ᗮ) (hx : x ∈ sphere 0 1) :
      F (stereoInvFun hv (D.chart x) : E) =
        (stereoInvFun hv (ellipsoidRoundingTrack A 1 (A (r • x))) : E) := by
    change R (T (F₀ (stereoInvFun hv (D.chart x) : E))) = _
    rw [htranslate x (sphere_subset_closedBall hx)]
    exact hRtrack _ ⟨r • x, hscaled ▸ ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨r, hr, hr1, F, ?_, ?_, ?_, (C₀ ∪ Cₜ) ∪ Cᵣ, (hC₀.union hCₜ).union hCᵣ, ?_⟩
  · intro y
    change ‖R (T (F₀ y))‖ = ‖y‖
    rw [hRnorm, hTnorm, hF₀norm]
  · calc
      F '' ((fun w => (stereoInvFun hv w : E)) '' D.boundary) =
          (fun x => (stereoInvFun hv (ellipsoidRoundingTrack A 1 (A (r • x))) : E)) ''
            sphere 0 1 := by
        change F '' ((fun w => (stereoInvFun hv w : E)) '' (D.chart '' sphere 0 1)) = _
        rw [image_image, image_image]
        exact image_congr hboundary
      _ = (fun w => (stereoInvFun hv w : E)) ''
          (ellipsoidRoundingTrack A 1 '' (A '' sphere 0 r)) := by
        rw [← hAscaled, image_image, image_image]
      _ = (fun w => (stereoInvFun hv w : E)) '' sphere 0 r := by
        rw [ellipsoidRoundingTrack_image_sphere A hr]
  · intro x hx hbad
    have hTv : T (F₀ (stereoInvFun hv (D.chart x) : E)) = v :=
      R.injective (hbad.trans hRzero.symm)
    have hF₀v : F₀ (stereoInvFun hv (D.chart x) : E) = v :=
      T.injective (hTv.trans hTzero.symm)
    rw [hF₀track x hx] at hF₀v
    exact stereoInvFun_ne_north_pole hv _ (Subtype.ext hF₀v)
  · intro y hy
    have hy0 : y ∉ C₀ := fun h => hy (Or.inl (Or.inl h))
    have hyt : y ∉ Cₜ := fun h => hy (Or.inl (Or.inr h))
    have hyr : y ∉ Cᵣ := fun h => hy (Or.inr h)
    change R (T (F₀ y)) = y
    rw [hF₀fix y hy0, hTfix y hyt, hRfix y hyr]

end PoincareConjecture.M25.Topology3D
