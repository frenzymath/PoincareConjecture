import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.Cylindrical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Collar



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev axis : E3 := EuclideanSpace.single 2 1


def planarCapLift (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  horizontalFamilyLift (fun _ => A) (A.contDiff.comp contDiff_snd)
    (A.symm.contDiff.comp contDiff_snd)

theorem planarCapLift_apply (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : E3) :
    planarCapLift A p = sliceAtHeight (p 2) (A (horizontal p)) :=
  horizontalFamilyLift_apply _ _ _ p

@[simp] theorem planarCapLift_height
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : E3) :
    planarCapLift A p 2 = p 2 := horizontalFamilyLift_height _ _ _ p

private theorem axis_inner (p : E3) : inner Real axis p = p 2 := by
  simp [axis, EuclideanSpace.inner_single_left]

private theorem axis_projection_norm (p : E3) :
    ‖(Hemisphere.Plane axis).orthogonalProjectionOnto p‖ = ‖horizontal p‖ := by
  have hv : ‖axis‖ = 1 := by simp [axis]
  have hp : ((Hemisphere.Plane axis).orthogonalProjectionOnto p : E3) =
      vector (p 0) (p 1) 0 := by
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton Real hv, axis_inner]
    ext i
    fin_cases i <;> simp [axis, vector]
  have hn : ‖(Hemisphere.Plane axis).orthogonalProjectionOnto p‖ ^ 2 =
      ‖horizontal p‖ ^ 2 := by
    change ‖((Hemisphere.Plane axis).orthogonalProjectionOnto p : E3)‖ ^ 2 = _
    rw [hp, EuclideanSpace.norm_sq_eq, norm_sq_two]
    simp [Fin.sum_univ_three, vector, horizontal]
  nlinarith [norm_nonneg ((Hemisphere.Plane axis).orthogonalProjectionOnto p),
    norm_nonneg (horizontal p)]

private theorem image_slice_of_membership
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (S : Set E3) (K : Set E2)
    (t : Real) (hS : ∀ p : E3, p 2 = t → (p ∈ S ↔ horizontal p ∈ K)) :
    (planarCapLift A '' S) ∩ {p : E3 | p 2 = t} =
      sliceAtHeight t '' (A '' K) := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
    have ht : x 2 = t := by
      change planarCapLift A x 2 = t at hxt
      simpa only [planarCapLift_height] using hxt
    exact ⟨A (horizontal x), ⟨horizontal x, (hS x ht).mp hx, rfl⟩,
      by rw [planarCapLift_apply, ht]⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hp : horizontal (sliceAtHeight t q) = q := by
      ext i
      fin_cases i <;> rfl
    refine ⟨⟨sliceAtHeight t q, (hS _ rfl).mpr (hp.symm ▸ hq), ?_⟩, rfl⟩
    rw [planarCapLift_apply, hp]
    rfl

theorem planarCapLift_northern_slice
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    (planarCapLift A '' boundedCylinderNorthernCap axis) ∩ {p : E3 | p 2 = t} =
      sliceAtHeight t '' (A '' sphere (0 : E2) 1) := by
  apply image_slice_of_membership
  intro p hp
  rw [mem_boundedCylinderNorthernCap_iff_of_height_lt_one (by simp [axis])
    (by rw [axis_inner, hp]; exact ht.2), axis_inner, hp, axis_projection_norm]
  simp only [ht.1, true_and, mem_sphere_zero_iff_norm]

theorem planarCapLift_body_slice
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    (planarCapLift A '' capBody axis) ∩ {p : E3 | p 2 = t} =
      sliceAtHeight t '' (A '' closedBall (0 : E2) 1) := by
  apply image_slice_of_membership
  intro p hp
  rw [mem_capBody_iff_of_height_lt_one (by simp [axis])
    (by rw [axis_inner, hp]; exact ht.2), axis_inner, hp, axis_projection_norm]
  simp only [ht.1, true_and, mem_closedBall_zero_iff]



theorem exists_profile_cap_with_canonical_collar {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p, G p 2 = p 2) ∧
      (∀ t : Real, |t| ≤ 1 / 16 → ∀ q : E2,
        G (tangentPlanarLatitude t q) = sliceAtHeight t
          (profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num) q)) ∧
      (∀ t ∈ Icc (0 : Real) (1 / 16),
        (G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})) ∩ {p | p 2 = t} =
          (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num)) '' boundedCylinderNorthernCap axis) ∩
              {p | p 2 = t}) ∧
      (∀ t ∈ Icc (0 : Real) (1 / 16),
        (G '' (closedBall (0 : E3) 1 ∩ {p | 0 ≤ p 2})) ∩ {p | p 2 = t} =
          (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num)) '' capBody axis) ∩ {p | p 2 = t}) := by
  obtain ⟨D, hDh, _, hmotion, hslices⟩ := exists_cylindrical_profile_cap hρ H a R
  let G := (profileCapShear hρ H a R).trans D
  have hGh (p : E3) : G p 2 = p 2 := by
    change D (profileCapShear hρ H a R p) 2 = p 2
    rw [hDh, profileCapShear_two]
  have hupper (S : Set E3) (t : Real) (ht : 0 ≤ t) :
      (G '' (S ∩ {p | 0 ≤ p 2})) ∩ {p | p 2 = t} =
        (D '' (profileCapShear hρ H a R '' S)) ∩ {p | p 2 = t} := by
    rw [image_image]
    change (G '' (S ∩ {p | 0 ≤ p 2})) ∩ {p | p 2 = t} =
      (G '' S) ∩ {p | p 2 = t}
    ext p
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hh⟩
      exact ⟨⟨x, hx.1, rfl⟩, hh⟩
    · rintro ⟨⟨x, hx, rfl⟩, hh⟩
      refine ⟨⟨x, ⟨hx, ?_⟩, rfl⟩, hh⟩
      change G x 2 = t at hh
      rw [hGh] at hh
      change 0 ≤ x 2
      rw [hh]
      exact ht
  refine ⟨G, hGh, hmotion, ?_, ?_⟩
  · intro t ht
    rw [hupper _ t ht.1, (hslices t (by rw [abs_of_nonneg ht.1]; exact ht.2)).2,
      planarCapLift_northern_slice _ ⟨ht.1, by linarith [ht.2]⟩]
  · intro t ht
    rw [hupper _ t ht.1, (hslices t (by rw [abs_of_nonneg ht.1]; exact ht.2)).1,
      planarCapLift_body_slice _ ⟨ht.1, by linarith [ht.2]⟩]

private theorem northern_collar_eq_of_slices (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hG : ∀ p, G p 2 = p 2) (S T : Set E3)
    (hT : ∀ p ∈ T, 0 ≤ p 2)
    (hslices : ∀ t ∈ Icc (0 : Real) (1 / 16),
      (G '' (S ∩ {p | 0 ≤ p 2})) ∩ {p | p 2 = t} = T ∩ {p | p 2 = t}) :
    (G '' (S ∩ {p | 0 ≤ p 2})) ∩ {p | |p 2| < 1 / 16} =
      T ∩ {p | |p 2| < 1 / 16} := by
  ext p
  constructor
  · rintro ⟨hp, ht⟩
    have hp0 : 0 ≤ p 2 := by
      obtain ⟨q, hq, rfl⟩ := hp
      rw [hG]
      exact hq.2
    have he := hslices (p 2) ⟨hp0, (le_abs_self (p 2)).trans ht.le⟩
    exact ⟨((Set.ext_iff.mp he p).mp ⟨hp, rfl⟩).1, ht⟩
  · rintro ⟨hp, ht⟩
    have he := hslices (p 2) ⟨hT p hp, (le_abs_self (p 2)).trans ht.le⟩
    exact ⟨((Set.ext_iff.mp he p).mpr ⟨hp, rfl⟩).1, ht⟩



theorem exists_profile_cap_common_open_collar {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p, G p 2 = p 2) ∧
      ∃ U : Set E3, IsOpen U ∧ {p : E3 | p 2 = 0} ⊆ U ∧
        (G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})) ∩ U =
          (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num)) '' boundedCylinderNorthernCap axis) ∩ U ∧
        (G '' (closedBall (0 : E3) 1 ∩ {p | 0 ≤ p 2})) ∩ U =
          (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num)) '' capBody axis) ∩ U := by
  obtain ⟨G, hG, _, hsphere, hbody⟩ := exists_profile_cap_with_canonical_collar hρ H a R
  refine ⟨G, hG, {p : E3 | |p 2| < 1 / 16}, ?_, ?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · intro p hp
    change |p 2| < 1 / 16
    change p 2 = 0 at hp
    rw [hp]
    norm_num
  · apply northern_collar_eq_of_slices G hG _ _ _ hsphere
    rintro p ⟨q, hq, rfl⟩
    rw [planarCapLift_height]
    exact (axis_inner q) ▸ height_nonneg_of_mem_boundedCylinderNorthernCap hq
  · apply northern_collar_eq_of_slices G hG _ _ _ hbody
    rintro p ⟨q, hq, rfl⟩
    rw [planarCapLift_height]
    exact (axis_inner q) ▸ hq.2

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
