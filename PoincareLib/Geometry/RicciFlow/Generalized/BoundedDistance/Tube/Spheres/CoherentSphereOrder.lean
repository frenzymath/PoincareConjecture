import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderSphereOrder

/-!
# Three fixed cylinder spheres and a bounded connecting set

A connected set from the first sphere to the middle sphere misses the
high sphere. Together with the common end orientation, this determines
the middle sphere's signs at the original base and the high witness.
Source: Morgan--Tian Claim 10.8, p. 254; M28 derivation 123.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M28

variable {X : Type*} [TopologicalSpace X]

/-- Three coherently oriented essential spheres place the base and high
witness on opposite sides of the middle sphere. The connecting set and
the high carrier are actual connected sets, with explicit exclusions.
Source: Claim 10.8, p. 254; M28 derivation 123. -/
theorem cylinderSignedHeight_middle_signs
    (phiS phiC phiH : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
    (hCpos : ∀ x, cylinderSignedHeight phiC x = 0 → 0 < cylinderSignedHeight phiS x)
    (hHpos : ∀ x, cylinderSignedHeight phiH x = 0 → 0 < cylinderSignedHeight phiS x)
    (hCH : ∀ x, cylinderSignedHeight phiC x = 0 → cylinderSignedHeight phiH x ≠ 0)
    (hlow : ∃ x, cylinderSignedHeight phiS x < 0 ∧
      cylinderSignedHeight phiC x < 0 ∧ cylinderSignedHeight phiH x < 0)
    (hhigh : ∃ x, 0 < cylinderSignedHeight phiS x ∧
      0 < cylinderSignedHeight phiC x ∧ 0 < cylinderSignedHeight phiH x)
    {b q z p : X} (hb : cylinderSignedHeight phiS b = 0)
    (hq : cylinderSignedHeight phiC q = 0) (hz : cylinderSignedHeight phiH z = 0)
    {K P : Set X} (hK : IsPreconnected K) (hbK : b ∈ K) (hqK : q ∈ K)
    (havoidK : ∀ x ∈ K, cylinderSignedHeight phiH x ≠ 0)
    (hP : IsPreconnected P) (hzP : z ∈ P) (hpP : p ∈ P)
    (havoidP : ∀ x ∈ P, cylinderSignedHeight phiC x ≠ 0) :
    cylinderSignedHeight phiC b < 0 ∧ 0 < cylinderSignedHeight phiC p := by
  obtain ⟨l, hlS, hlC, hlH⟩ := hlow
  obtain ⟨r, hrS, hrC, hrH⟩ := hhigh
  have hSC : ∀ x, cylinderSignedHeight phiS x = 0 →
      cylinderSignedHeight phiC x ≠ 0 := by
    intro x hxS hxC
    have h := hCpos x hxC
    rw [hxS] at h
    exact lt_irrefl _ h
  have hSH : ∀ x, cylinderSignedHeight phiS x = 0 →
      cylinderSignedHeight phiH x ≠ 0 := by
    intro x hxS hxH
    have h := hHpos x hxH
    rw [hxS] at h
    exact lt_irrefl _ h
  have hbC : cylinderSignedHeight phiC b < 0 := by
    rcases cylinderSignedHeight_opposite_order phiS phiC hSC
      ⟨l, hlS, hlC⟩ ⟨r, hrS, hrC⟩ with h | h
    · exact h.2 b hb
    · exact False.elim ((not_lt_of_ge (hCpos q hq).le) (h.1 q hq))
  have hbH : cylinderSignedHeight phiH b < 0 := by
    rcases cylinderSignedHeight_opposite_order phiS phiH hSH
      ⟨l, hlS, hlH⟩ ⟨r, hrS, hrH⟩ with h | h
    · exact h.2 b hb
    · exact False.elim ((not_lt_of_ge (hHpos z hz).le) (h.1 z hz))
  have hqH : cylinderSignedHeight phiH q < 0 :=
    hK.gt_of_ne (continuous_cylinderSignedHeight phiH).continuousOn
      havoidK ⟨b, hbK, hbH⟩ hqK
  have hHC : ∀ x, cylinderSignedHeight phiH x = 0 →
      0 < cylinderSignedHeight phiC x := by
    rcases cylinderSignedHeight_opposite_order phiC phiH hCH
      ⟨l, hlC, hlH⟩ ⟨r, hrC, hrH⟩ with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (h.2 q hq).le) hqH)
  exact ⟨hbC, hP.lt_of_ne (continuous_cylinderSignedHeight phiC).continuousOn
    havoidP ⟨z, hzP, hHC z hz⟩ hpP⟩

end PoincareMT.M28
