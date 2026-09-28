import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.WholeCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1

def capPhysicalFrame {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  ((graphCoordinates (fun _ : E2 => (0 : Real)) contDiff_const).symm.trans
    (ContinuousLinearEquiv.prodComm Real E2 Real).toDiffeomorph).trans
      (((ContinuousLinearEquiv.refl Real Real).prodCongr
        J.symm.toContinuousLinearEquiv).trans (heightCoordinates hv)).toDiffeomorph

theorem capPhysicalFrame_apply {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (p : E3) :
    capPhysicalFrame hv J p = p 2 • v + (J.symm (horizontal p) : E3) := by
  change (p 2 - 0) • v + (J.symm (horizontal p) : E3) = _
  rw [sub_zero]

@[simp] theorem capPhysicalFrame_height {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (p : E3) :
    inner Real v (capPhysicalFrame hv J p) = p 2 := by
  rw [capPhysicalFrame_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm (horizontal p)).property]

@[simp] theorem capPhysicalFrame_projection {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (p : E3) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (capPhysicalFrame hv J p) =
      J.symm (horizontal p) := by
  rw [capPhysicalFrame_apply]
  simp [Hemisphere.Plane]

theorem capPhysicalFrame_norm {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (p : E3) :
    ‖capPhysicalFrame hv J p‖ = ‖p‖ := by
  have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (J.symm (horizontal p)).property
  have he : ‖capPhysicalFrame hv J p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [capPhysicalFrame_apply, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, inner_smul_left, hz,
      mul_zero, add_zero]
    change |p 2| ^ 2 + ‖J.symm (horizontal p)‖ ^ 2 = ‖p‖ ^ 2
    rw [J.symm.norm_map]
    rw [EuclideanSpace.norm_sq_eq (horizontal p), EuclideanSpace.norm_sq_eq p]
    simp only [Fin.sum_univ_two, Fin.sum_univ_three, horizontal, WithLp.ofLp_toLp,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    ring
  nlinarith [norm_nonneg (capPhysicalFrame hv J p), norm_nonneg p]

theorem capPhysicalFrame_smul {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (s : Real) (p : E3) :
    capPhysicalFrame hv J (s • p) = s • capPhysicalFrame hv J p := by
  have hh : horizontal (s • p) = s • horizontal p := by ext i; fin_cases i <;> rfl
  simp [capPhysicalFrame_apply, hh, smul_add, smul_smul]

theorem capPhysicalFrame_northernCap {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) :
    capPhysicalFrame hv J '' boundedCylinderNorthernCap axis =
      boundedCylinderNorthernCap v := by
  let P := capPhysicalFrame hv J
  have hrad (p : S2) : boundedCylinderRadius v
      ⟨P p, by simpa only [mem_sphere_zero_iff_norm, P, capPhysicalFrame_norm] using p.property⟩ =
        boundedCylinderRadius axis p := by
    have he : inner Real v (P p) = inner Real axis (p : E3) := by
      simp [P, axis, EuclideanSpace.inner_single_left]
    unfold boundedCylinderRadius
    rw [he]
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨⟨P p, by simpa only [mem_sphere_zero_iff_norm, P, capPhysicalFrame_norm] using p.property⟩,
      ?_, ?_⟩
    · simpa [P, axis, EuclideanSpace.inner_single_left] using hp
    · dsimp only
      rw [hrad, capPhysicalFrame_smul]
  · rintro ⟨p, hp, rfl⟩
    have hn : P.symm p ∈ sphere (0 : E3) 1 := by
      rw [mem_sphere_zero_iff_norm, ← capPhysicalFrame_norm hv J (P.symm p)]
      change ‖P (P.symm p)‖ = 1
      rw [P.apply_symm_apply]
      exact norm_eq_of_mem_sphere p
    let q : S2 := ⟨P.symm p, hn⟩
    have hq : P q = p := P.apply_symm_apply p
    have hr : boundedCylinderRadius axis q = boundedCylinderRadius v p := by
      rw [← hrad q]
      congr 1
      exact Subtype.ext hq
    refine ⟨boundedCylinderRadius axis q • (q : E3), ⟨q, ?_, rfl⟩, ?_⟩
    · have he := capPhysicalFrame_height hv J q
      change inner Real v (P q) = _ at he
      rw [hq] at he
      simpa [axis, EuclideanSpace.inner_single_left, ← he] using hp
    · rw [capPhysicalFrame_smul, hq, hr]

def capPhysicalCoordinates {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (c z : Real) (hz : z ≠ 0) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  (capPhysicalFrame hv J).trans (liftPlaneDiffeomorph hv c z hz
    (Diffeomorph.refl 𝓘(Real, Hemisphere.Plane v) (Hemisphere.Plane v) ∞))

theorem capPhysicalCoordinates_apply {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (c z : Real) (hz : z ≠ 0) (p : E3) :
    capPhysicalCoordinates hv J c z hz p =
      (c + z * p 2) • v + (J.symm (horizontal p) : E3) := by
  simp [capPhysicalCoordinates]

@[simp] theorem capPhysicalCoordinates_height {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (c z : Real) (hz : z ≠ 0) (p : E3) :
    inner Real v (capPhysicalCoordinates hv J c z hz p) = c + z * p 2 := by
  rw [capPhysicalCoordinates_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm (horizontal p)).property]

def capPlanarCoordinates {v : E3} (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
  (J.symm.toContinuousLinearEquiv.toDiffeomorph.trans B).trans
    J.toContinuousLinearEquiv.toDiffeomorph

theorem capPhysicalCoordinates_liftedCap {v : E3} (hv : ‖v‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) (c z : Real) (hz : z ≠ 0)
    (B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    capPhysicalCoordinates hv J c z hz ''
        (planarCapLift (capPlanarCoordinates J B) '' boundedCylinderNorthernCap axis) =
      liftPlaneDiffeomorph hv c z hz B '' boundedCylinderNorthernCap v := by
  rw [← capPhysicalFrame_northernCap hv J, image_image, image_image]
  apply image_congr
  intro p _
  rw [capPhysicalCoordinates_apply, liftPlaneDiffeomorph_apply,
    capPhysicalFrame_height, capPhysicalFrame_projection, planarCapLift_height,
    planarCapLift_apply]
  have hh (q : E2) : horizontal (sliceAtHeight (p 2) q) = q := by
    ext i
    fin_cases i <;> rfl
  rw [hh]
  change (c + z * p 2) • v + (J.symm (J (B (J.symm (horizontal p)))) : E3) = _
  rw [J.symm_apply_apply]

theorem exists_physical_relative_cap_replacement
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (c z : Real) (hz : 0 < z)
    (B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hGheight : ∀ p, G p 2 = p 2)
    {σ : Real} (hσ : 0 < σ)
    (hG : ∀ t, |t| ≤ σ → ∀ q : E2,
      G (tangentPlanarLatitude t q) = sliceAtHeight t (capPlanarCoordinates J B q)) :
    ∃ (ε : Real) (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < ε ∧ (∀ p : E3, inner Real v p ≤ c + ε → E p = p) ∧
      E '' (liftPlaneDiffeomorph hv c z hz.ne' B '' boundedCylinderNorthernCap v) =
        capPhysicalCoordinates hv J c z hz.ne' ''
          (G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})) := by
  obtain ⟨η, E, hη, hfix, hcap⟩ :=
    exists_relative_canonical_cap_replacement_of_cylindrical_coordinates
      (capPlanarCoordinates J B) G hGheight hσ hG
  let C := capPhysicalCoordinates hv J c z hz.ne'
  refine ⟨z * η, (C.symm.trans E).trans C, mul_pos hz hη, ?_, ?_⟩
  · intro p hp
    have he := capPhysicalCoordinates_height hv J c z hz.ne' (C.symm p)
    change inner Real v (C (C.symm p)) = _ at he
    rw [C.apply_symm_apply] at he
    have ht : C.symm p 2 ≤ η := by nlinarith
    change C (E (C.symm p)) = p
    rw [hfix _ ht, C.apply_symm_apply]
  · rw [← capPhysicalCoordinates_liftedCap hv J c z hz.ne' B]
    change (C ∘ E ∘ C.symm) '' (C '' _) = C '' _
    rw [image_comp, image_comp, C.symm_image_image, hcap]

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
