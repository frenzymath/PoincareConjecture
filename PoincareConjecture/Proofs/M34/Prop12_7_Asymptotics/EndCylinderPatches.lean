import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndTranslation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



def endCenteredCylinderMap (e : StandardCylindricalEnd g) (H : ℝ) :
    StandardCylinderSpace → StandardCapSpace := e.coordinate ∘ cylinderAxialTranslation H



def endCenteredCylinderInverse (e : StandardCylindricalEnd g) (H : ℝ) :
    StandardCapSpace → StandardCylinderSpace := cylinderAxialTranslation (-H) ∘ e.inverse



theorem endCenteredCylinderMap_contMDiffAt (e : StandardCylindricalEnd g) (H : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2 + H) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (endCenteredCylinderMap e H) z :=
  (end_coordinate_contMDiffAt e hz).comp z
    (cylinderAxialTranslation_contMDiff H).contMDiffAt



def endCenteredCylinderPatch (e : StandardCylindricalEnd g)
    {L H : ℝ} (hL : 0 < L) (hH : L < H) (q : UnitTwoSphere) :
    StandardCylinderPatch L (e.coordinate (q, H)) := by
  let V : Set StandardCylinderSpace := univ ×ˢ Ioo (H - L) (H + L)
  have hpos (z : StandardCylinderSpace) (hz : z ∈ V) : 0 < z.2 := by
    have hz0 := hz.2.1
    linarith
  have hshift (z : StandardCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-L) L) :
      0 < z.2 + H := by
    have hz0 := hz.2.1
    linarith
  refine {
    length_pos := hL
    carrier := e.coordinate '' V
    carrier_open := end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioo) hpos
    coordinate := endCenteredCylinderMap e H
    inverse := endCenteredCylinderInverse e H
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := ?_
    inverse_domain := ?_
    coordinate_smooth := ?_
    inverse_smooth := ?_
    center_sphere := ⟨q, ?_⟩ }
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨cylinderAxialTranslation H z, ⟨mem_univ _, ?_⟩, rfl⟩
      change H - L < z.2 + H ∧ z.2 + H < H + L
      constructor <;> linarith [hz.2.1, hz.2.2]
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(z.1, z.2 - H), ⟨mem_univ _, ?_⟩, ?_⟩
      · change -L < z.2 - H ∧ z.2 - H < L
        constructor <;> linarith [hz.2.1, hz.2.2]
      · simp [endCenteredCylinderMap, cylinderAxialTranslation]
  · intro z hz
    have hi := e.coordinate_left_inverse
      (show cylinderAxialTranslation H z ∈ univ ×ˢ Ici (0 : ℝ) from
        ⟨mem_univ _, (hshift z hz).le⟩)
    simp only [endCenteredCylinderMap, endCenteredCylinderInverse, Function.comp_apply, hi]
    simp [cylinderAxialTranslation]
  · rintro _ ⟨z, hz, rfl⟩
    have hi := e.coordinate_left_inverse ⟨mem_univ _, (hpos z hz).le⟩
    simp only [endCenteredCylinderMap, endCenteredCylinderInverse, Function.comp_apply, hi]
    simp [cylinderAxialTranslation]
  · rintro _ ⟨z, hz, rfl⟩
    have hi := e.coordinate_left_inverse ⟨mem_univ _, (hpos z hz).le⟩
    simp only [endCenteredCylinderInverse, Function.comp_apply, hi, cylinderAxialTranslation]
    change -L < z.2 + -H ∧ z.2 + -H < L
    constructor <;> linarith [hz.2.1, hz.2.2]
  · intro z hz
    exact (endCenteredCylinderMap_contMDiffAt e H (hshift z hz)).contMDiffWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    exact ((cylinderAxialTranslation_contMDiff (-H)).contMDiffAt.comp (e.coordinate z)
      (end_inverse_contMDiffAt e (hpos z hz))).contMDiffWithinAt
  · simp [endCenteredCylinderMap, cylinderAxialTranslation]

end PoincareConjecture.M34
