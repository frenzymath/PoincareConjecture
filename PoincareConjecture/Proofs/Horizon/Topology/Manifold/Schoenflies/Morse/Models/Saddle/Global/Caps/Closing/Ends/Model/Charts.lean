import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.MeridianFactors

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

def coordinateReflection (k : Fin 3) : E3 ≃ₗᵢ[Real] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
    if i = k then LinearIsometryEquiv.neg Real else LinearIsometryEquiv.refl Real Real)

theorem coordinateReflection_apply (k : Fin 3) (p : E3) (i : Fin 3) :
    coordinateReflection k p i = if i = k then -p i else p i := by
  change (if i = k then LinearIsometryEquiv.neg Real else
    LinearIsometryEquiv.refl Real Real) (p i) = _
  split_ifs <;> rfl

private theorem coordinateReflection_involutive (k : Fin 3) (p : E3) :
    coordinateReflection k (coordinateReflection k p) = p := by
  ext i
  simp only [coordinateReflection_apply]
  split_ifs <;> simp

private theorem coordinateReflection_mem (k : Fin 3) (p : S2) :
    coordinateReflection k p ∈ sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm, (coordinateReflection k).norm_map]
  exact norm_eq_of_mem_sphere p

def sphereCoordinateReflection (k : Fin 3) : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞ where
  toFun p := ⟨coordinateReflection k p, coordinateReflection_mem k p⟩
  invFun p := ⟨coordinateReflection k p, coordinateReflection_mem k p⟩
  left_inv p := Subtype.ext (coordinateReflection_involutive k p)
  right_inv p := Subtype.ext (coordinateReflection_involutive k p)
  contMDiff_toFun := ((coordinateReflection k).contDiff.contMDiff.comp
    (contMDiff_coe_sphere (n := 2))).codRestrict_sphere (coordinateReflection_mem k)
  contMDiff_invFun := ((coordinateReflection k).contDiff.contMDiff.comp
    (contMDiff_coe_sphere (n := 2))).codRestrict_sphere (coordinateReflection_mem k)

theorem sphereCoordinateReflection_apply (k : Fin 3) (p : S2) (i : Fin 3) :
    (sphereCoordinateReflection k p : E3) i = if i = k then -(p : E3) i else (p : E3) i :=
  coordinateReflection_apply k p i

open Saddle.Nested

def meridianSphereChart (positive : Bool) (z : Real) : OpenPartialHomeomorph E2 S2 :=
  if positive then (negativeSphereChart z).trans
    (sphereCoordinateReflection 0).toHomeomorph.toOpenPartialHomeomorph
  else negativeSphereChart z

theorem meridianSphereChart_source (positive : Bool) (z : Real) :
    (meridianSphereChart positive z).source = coordinateDomain z := by
  cases positive
  · exact negativeSphereChart_source z
  · simp [meridianSphereChart, negativeSphereChart_source]

theorem meridianSphereChart_smooth (positive : Bool) (z : Real) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (meridianSphereChart positive z)
      (meridianSphereChart positive z).source := by
  cases positive
  · exact negativeSphereChart_smooth z
  · exact (sphereCoordinateReflection 0).contMDiff.comp_contMDiffOn
      ((negativeSphereChart_smooth z).mono inter_subset_left)

theorem meridianSphereChart_symm_smooth (positive : Bool) (z : Real) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (meridianSphereChart positive z).symm
      (meridianSphereChart positive z).target := by
  cases positive
  · exact (negativeSphereChart_symm_smooth z).contMDiffOn
  · exact ((negativeSphereChart_symm_smooth z).comp
      (sphereCoordinateReflection 0).symm.contMDiff).contMDiffOn

theorem meridianSphereChart_coe (positive : Bool) {z : Real} {q : E2}
    (hq : q ∈ coordinateDomain z) :
    (meridianSphereChart positive z q : E3) =
      Saddle.vector (if positive then chartRoot z q else -chartRoot z q) (q 1) (z+q 0) := by
  have hqs : q ∈ (negativeSphereChart z).source := negativeSphereChart_source z ▸ hq
  cases positive
  · exact negativeSphereChart_coe hqs
  · change (sphereCoordinateReflection 0 (negativeSphereChart z q) : E3) = _
    ext i
    rw [sphereCoordinateReflection_apply, negativeSphereChart_coe hqs]
    fin_cases i <;> simp

theorem meridianSphereChart_zero (positive : Bool) {z : Real} (hz : 0 < 1-z^2) :
    (meridianSphereChart positive z 0 : E3) =
      Saddle.vector (if positive then meridianRoot z else -meridianRoot z) 0 z := by
  rw [meridianSphereChart_coe positive (by simpa [coordinateDomain] using hz)]
  simp [chartRoot, meridianRoot]

theorem nested_height_meridianSphereChart (positive : Bool) {z : Real} {q : E2}
    (hq : q ∈ coordinateDomain z) :
    Saddle.Nested.height (meridianSphereChart positive z q) =
      meridianHeight (if positive then 3/10 else -(3/10)) z q := by
  have hr : (chartRoot z q)^2 = 1-(z+q 0)^2-(q 1)^2 := Real.sq_sqrt hq.le
  rw [Saddle.Nested.height_apply, meridianSphereChart_coe positive hq]
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, Saddle.vector_zero,
    Saddle.vector_one, Saddle.vector_two, neg_sq] <;>
    rw [hr] <;> dsimp [meridianHeight] <;> ring

theorem standard_height_meridianSphereChart (positive : Bool) {z : Real} {q : E2}
    (hq : q ∈ coordinateDomain z) :
    Saddle.height (meridianSphereChart positive z q) =
      -1+(z+q 0)+(z+q 0)^2+(q 1)^2 := by
  have hr : (chartRoot z q)^2 = 1-(z+q 0)^2-(q 1)^2 := Real.sq_sqrt hq.le
  rw [Saddle.height_apply, meridianSphereChart_coe positive hq]
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, Saddle.vector_zero,
    Saddle.vector_two, neg_sq] <;> rw [hr] <;> ring

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model
