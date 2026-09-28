import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Marking



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

private theorem norm_height_plane_sq {v : E3} (hv : ‖v‖ = 1)
    (t : Real) (q : Hemisphere.Plane v) :
    ‖t • v + (q : E3)‖ ^ 2 = t ^ 2 + ‖q‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, Real.norm_eq_abs, hv, inner_smul_left,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.property]



def extendPlaneIsometry {v w : E3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] Hemisphere.Plane w) : E3 ≃ₗᵢ[Real] E3 := by
  let L := ((heightCoordinates hv).symm.trans
    ((ContinuousLinearEquiv.refl Real Real).prodCongr J.toContinuousLinearEquiv)).trans
      (heightCoordinates hw)
  refine { L.toLinearEquiv with norm_map' := ?_ }
  intro x
  obtain ⟨⟨t, q⟩, rfl⟩ := (heightCoordinates hv).surjective x
  have hL : L (heightCoordinates hv (t, q)) = heightCoordinates hw (t, J q) := by
    change heightCoordinates hw
      (((ContinuousLinearEquiv.refl Real Real).prodCongr J.toContinuousLinearEquiv)
        ((heightCoordinates hv).symm (heightCoordinates hv (t, q)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  change ‖L (heightCoordinates hv (t, q))‖ = ‖heightCoordinates hv (t, q)‖
  rw [hL]
  have heq : ‖heightCoordinates hw (t, J q)‖ ^ 2 =
      ‖heightCoordinates hv (t, q)‖ ^ 2 := by
    rw [heightCoordinates_apply, heightCoordinates_apply,
      norm_height_plane_sq hw, norm_height_plane_sq hv, J.norm_map]
  nlinarith [norm_nonneg (heightCoordinates hw (t, J q)),
    norm_nonneg (heightCoordinates hv (t, q))]

theorem extendPlaneIsometry_apply {v w : E3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] Hemisphere.Plane w) (t : Real)
    (q : Hemisphere.Plane v) :
    extendPlaneIsometry hv hw J (t • v + (q : E3)) = t • w + (J q : E3) := by
  change heightCoordinates hw
    (((ContinuousLinearEquiv.refl Real Real).prodCongr J.toContinuousLinearEquiv)
      ((heightCoordinates hv).symm (heightCoordinates hv (t, q)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem extendPlaneIsometry_toSphere {v w : E3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (J : Hemisphere.Plane v ≃ₗᵢ[Real] Hemisphere.Plane w)
    (q : Hemisphere.Plane v) :
    extendPlaneIsometry hv hw J (Hemisphere.toSphere hv q : E3) =
      (Hemisphere.toSphere hw (J q) : E3) := by
  let L := extendPlaneIsometry hv hw J
  have hsum : L ((q : E3) + v) = (J q : E3) + w := by
    simpa only [one_smul, add_comm] using extendPlaneIsometry_apply hv hw J 1 q
  have hnorm : ‖(J q : E3) + w‖ = ‖(q : E3) + v‖ := by
    rw [← hsum, L.norm_map]
  change L (‖(q : E3) + v‖⁻¹ • ((q : E3) + v)) =
    ‖(J q : E3) + w‖⁻¹ • ((J q : E3) + w)
  rw [map_smul, hsum, hnorm]



theorem exists_marked_ball_equivalence
    (B₁ B₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (m₁ m₂ : E2 → S2)
    (hi₁ : InjOn m₁ (closedBall 0 1)) (hi₂ : InjOn m₂ (closedBall 0 1))
    (hl₁ : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m₁ x)
    (hl₂ : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m₂ x) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' (B₁ '' closedBall (0 : E3) 1) = B₂ '' closedBall (0 : E3) 1 ∧
      ∀ x ∈ closedBall (0 : E2) 1, D (B₁ (m₁ x : E3)) = B₂ (m₂ x : E3) := by
  obtain ⟨J₁, H₁, hB₁, _, _, hm₁, _⟩ :=
    Rounding.Normalization.exists_ambient_ball_normalization B₁ m₁ hi₁ hl₁
  obtain ⟨J₂, H₂, hB₂, _, _, hm₂, _⟩ :=
    Rounding.Normalization.exists_ambient_ball_normalization B₂ m₂ hi₂ hl₂
  let hv := norm_eq_of_mem_sphere (m₁ 0)
  let hw := norm_eq_of_mem_sphere (m₂ 0)
  let L := extendPlaneIsometry hv hw (J₁.symm.trans J₂)
  let P := L.toContinuousLinearEquiv.toDiffeomorph
  let D := (H₁.trans P).trans H₂.symm
  have hLball : P '' closedBall (0 : E3) 1 = closedBall 0 1 := by
    change L '' closedBall (0 : E3) 1 = _
    simpa only [map_zero] using L.image_closedBall (0 : E3) 1
  refine ⟨D, ?_, ?_⟩
  · apply H₂.injective.image_injective
    change H₂ '' (D '' (B₁ '' closedBall (0 : E3) 1)) =
      H₂ '' (B₂ '' closedBall (0 : E3) 1)
    rw [hB₂, image_image]
    change (fun y => H₂ (H₂.symm (P (H₁ y)))) '' (B₁ '' closedBall (0 : E3) 1) = _
    simp only [H₂.apply_symm_apply]
    rw [← image_image, hB₁, hLball]
  · intro x hx
    change H₂.symm (P (H₁ (B₁ (m₁ x : E3)))) = B₂ (m₂ x : E3)
    rw [hm₁ x hx]
    have hP : P (Hemisphere.toSphere hv (J₁ x) : E3) =
        (Hemisphere.toSphere hw (J₂ x) : E3) := by
      change L (Hemisphere.toSphere hv (J₁ x) : E3) = _
      rw [extendPlaneIsometry_toSphere]
      simp only [LinearIsometryEquiv.trans_apply, J₁.symm_apply_apply]
    rw [hP, ← hm₂ x hx, H₂.symm_apply_apply]



theorem exists_ball_equivalence_fixing_common_disk
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Function.Injective g)
    (hgd : ∀ x, Function.Injective (fderiv Real g x))
    {r : Real} (hr : 0 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    (p0 : S2) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      D '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
      ∀ y ∈ g '' closedBall (0 : E2) r, D y = y := by
  obtain ⟨m, hmi, hml, hm, hmrange⟩ := exists_ambient_disk_marking_at_radius B g hg hgi hgd
    hr hB p0
  obtain ⟨n, hni, hnl, hn, _⟩ := exists_ambient_disk_marking_at_radius L g hg hgi hgd hr hL p0
  obtain ⟨D, hDB, hDmark⟩ := exists_marked_ball_equivalence B L m n hmi hni hml hnl
  refine ⟨D, hDB, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hmrange.symm ▸ hy
  change D (B (m x : E3)) = B (m x : E3)
  rw [hDmark x hx, hn x hx, hm x hx]

end Poincare.Manifold.Schoenflies.Reverse
