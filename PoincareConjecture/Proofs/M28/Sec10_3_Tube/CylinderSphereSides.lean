import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCoordinates
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.M28

variable {X : Type u} [TopologicalSpace X]

noncomputable def cylinderSignedHeight
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) (x : X) : ℝ :=
  ((φ x).2 : ℝ) - 1 / 2

theorem continuous_cylinderSignedHeight
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    Continuous (cylinderSignedHeight φ) :=
  (continuous_subtype_val.comp (continuous_snd.comp φ.continuous)).sub continuous_const

theorem isOpenMap_cylinderSignedHeight
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    IsOpenMap (cylinderSignedHeight φ) :=
  (isOpenMap_sub_right (1 / 2 : ℝ)).comp
    (isOpen_Ioo.isOpenMap_subtype_val.comp (isOpenMap_snd.comp φ.isOpenMap))

private theorem sphere_univ_preconnected : IsPreconnected (univ : Set UnitTwoSphere) := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  exact isPreconnected_univ

private theorem lower_interval_preconnected :
    IsPreconnected {s : Ioo (0 : ℝ) 1 | (s : ℝ) < 1 / 2} := by
  have hrange : Ioo (0 : ℝ) (1 / 2) ⊆ range (Subtype.val : Ioo (0 : ℝ) 1 → ℝ) := by
    intro s hs
    exact ⟨⟨s, hs.1, hs.2.trans (by norm_num)⟩, rfl⟩
  have hh := (isPreconnected_Ioo : IsPreconnected (Ioo (0 : ℝ) (1 / 2))).preimage_of_isOpenMap
    Subtype.val_injective isOpen_Ioo.isOpenMap_subtype_val hrange
  convert hh using 1
  ext s
  exact ⟨fun hs => ⟨s.property.1, hs⟩, fun hs => hs.2⟩

private theorem upper_interval_preconnected :
    IsPreconnected {s : Ioo (0 : ℝ) 1 | (1 / 2 : ℝ) < s} := by
  have hrange : Ioo (1 / 2 : ℝ) 1 ⊆ range (Subtype.val : Ioo (0 : ℝ) 1 → ℝ) := by
    intro s hs
    exact ⟨⟨s, (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1, hs.2⟩, rfl⟩
  have hh := (isPreconnected_Ioo : IsPreconnected (Ioo (1 / 2 : ℝ) 1)).preimage_of_isOpenMap
    Subtype.val_injective isOpen_Ioo.isOpenMap_subtype_val hrange
  convert hh using 1
  ext s
  exact ⟨fun hs => ⟨hs, s.property.2⟩, fun hs => hs.1⟩

theorem isPreconnected_cylinderSignedHeight_negative
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    IsPreconnected {x | cylinderSignedHeight φ x < 0} := by
  have hh := (sphere_univ_preconnected.prod lower_interval_preconnected).preimage_of_isOpenMap
    φ.injective φ.isOpenMap (fun x _ => φ.surjective x)
  convert hh using 1
  ext x
  simp [cylinderSignedHeight]

theorem isPreconnected_cylinderSignedHeight_positive
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    IsPreconnected {x | 0 < cylinderSignedHeight φ x} := by
  have hh := (sphere_univ_preconnected.prod upper_interval_preconnected).preimage_of_isOpenMap
    φ.injective φ.isOpenMap (fun x _ => φ.surjective x)
  convert hh using 1
  ext x
  simp [cylinderSignedHeight]

theorem isPreconnected_cylinderSignedHeight_zero
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    IsPreconnected {x | cylinderSignedHeight φ x = 0} := by
  let c : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hh :=
    (sphere_univ_preconnected.prod (isPreconnected_singleton (x := c))).preimage_of_isOpenMap
      φ.injective φ.isOpenMap (fun x _ => φ.surjective x)
  convert hh using 1
  ext x
  simp [cylinderSignedHeight, c, Subtype.ext_iff, sub_eq_zero]

theorem closure_cylinderSignedHeight_negative
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    closure {x | cylinderSignedHeight φ x < 0} =
      {x | cylinderSignedHeight φ x ≤ 0} := by
  have hh := (isOpenMap_cylinderSignedHeight φ).preimage_closure_eq_closure_preimage
    (continuous_cylinderSignedHeight φ) (Iio (0 : ℝ))
  rw [closure_Iio] at hh
  exact hh.symm

theorem closure_cylinderSignedHeight_positive
    (φ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    closure {x | 0 < cylinderSignedHeight φ x} =
      {x | 0 ≤ cylinderSignedHeight φ x} := by
  have hh := (isOpenMap_cylinderSignedHeight φ).preimage_closure_eq_closure_preimage
    (continuous_cylinderSignedHeight φ) (Ioi (0 : ℝ))
  rw [closure_Ioi] at hh
  exact hh.symm

end PoincareConjecture.M28
