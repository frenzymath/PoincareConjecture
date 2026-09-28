import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.CornerFamilyTransport
import Mathlib.Topology.Homeomorph.Lemmas









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem mem_cornerMap_image (c : Fin 3) (s : Set (ℝ × ℝ)) (x : ℝ × ℝ) :
    x ∈ cornerMap c '' s ↔ cornerMap c x ∈ s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [cornerMap_involutive]
  · intro hx
    exact ⟨cornerMap c x, hx, cornerMap_involutive c x⟩

theorem cornerMap_image_image (c : Fin 3) (s : Set (ℝ × ℝ)) :
    cornerMap c '' (cornerMap c '' s) = s := by
  ext x
  rw [mem_cornerMap_image, mem_cornerMap_image, cornerMap_involutive]

theorem cornerMap_image_difference (c : Fin 3) (s t : Set (ℝ × ℝ)) :
    cornerMap c '' (s \ t) = (cornerMap c '' s) \ (cornerMap c '' t) := by
  ext x
  simp only [mem_cornerMap_image, mem_sdiff]

theorem cornerMap_image_arc_complement {ι : Type*} (c : Fin 3) (D : ι → Set (ℝ × ℝ)) :
    cornerMap c '' (base \ ⋃ i, D i) = base \ ⋃ i, cornerMap c '' D i := by
  rw [cornerMap_image_difference, cornerMap_image_base, image_iUnion]

theorem cornerMap_image_arc_component {ι : Type*} (c : Fin 3) (D : ι → Set (ℝ × ℝ))
    {x : ℝ × ℝ} (hx : x ∈ base \ ⋃ i, cornerMap c '' D i) :
    cornerMap c '' connectedComponentIn (base \ ⋃ i, cornerMap c '' D i) x =
      connectedComponentIn (base \ ⋃ i, D i) (cornerMap c x) := by
  have h := (cornerHomeomorph c).image_connectedComponentIn hx
  change cornerMap c '' connectedComponentIn (base \ ⋃ i, cornerMap c '' D i) x =
    connectedComponentIn (cornerMap c '' (base \ ⋃ i, cornerMap c '' D i)) (cornerMap c x) at h
  rw [cornerMap_image_arc_complement] at h
  simpa only [cornerMap_image_image] using h



theorem exists_corner_image_square_chart (c : Fin 3) {M : Set (ℝ × ℝ)}
    (C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M)
    (hC : C.IsFinitePL) :
    ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ (cornerMap c '' M),
      G.IsFinitePL ∧ ∀ x, (G x : ℝ × ℝ) = cornerMap c (C x) := by
  obtain ⟨_, ⟨K, hK, hKM, _⟩, _⟩ := hC.symm
  have hF : FinitePiecewiseAffineOn (cornerMap c) M :=
    ⟨K, hK, hKM, K.affineOnFaces_affine (cornerMap c)⟩
  obtain ⟨H, hH, hHval⟩ := hF.exists_homeomorph_image (cornerMap_involutive c).injective.injOn
  exact ⟨C.trans H, hC.trans hH, fun x => hHval (C x)⟩

end PoincareConjecture.M76.TriangleCorner
