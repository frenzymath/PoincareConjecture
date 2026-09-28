import PoincareConjecture.Definitions.M74ConnectedSumReduction
import Mathlib.Geometry.Euclidean.Inversion.Basic










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M74

local notation "E4" => EuclideanSpace ℝ (Fin 4)

private instance sphere_finrank : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

private noncomputable def sphereAntipodal :
    Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞ where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_neg_sphere
  contMDiff_invFun := contMDiff_neg_sphere



noncomputable def standardSphereChart (v : ThreeSphere) :
    OpenPartialHomeomorph ThreeSphere StandardCapSpace := chartAt StandardCapSpace (-v)

private theorem standardSphereChart_eq_stereographic (v : ThreeSphere) :
    standardSphereChart v = stereographic' 3 v := by
  change stereographic' 3 (- -v) = stereographic' 3 v
  rw [neg_neg]



@[simp] theorem standardSphereChart_source (v : ThreeSphere) :
    (standardSphereChart v).source = {v}ᶜ := by
  rw [standardSphereChart_eq_stereographic, stereographic'_source]



@[simp] theorem standardSphereChart_target (v : ThreeSphere) :
    (standardSphereChart v).target = univ := by
  rw [standardSphereChart_eq_stereographic, stereographic'_target]



theorem standardSphereChart_contMDiffOn (v : ThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (standardSphereChart v)
      (standardSphereChart v).source := contMDiffOn_chart



theorem standardSphereChart_symm_contMDiff (v : ThreeSphere) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (standardSphereChart v).symm := by
  apply contMDiffOn_univ.mp
  rw [← standardSphereChart_target v]
  exact contMDiffOn_chart_symm

private noncomputable def sphereCoordinates (v : ThreeSphere) :
    (ℝ ∙ (v : E4))ᗮ ≃ₗᵢ[ℝ] StandardCapSpace :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere v)).repr

private theorem standardSphereChart_symm_formula (v : ThreeSphere) (z : StandardCapSpace) :
    ((standardSphereChart v).symm z : E4) =
      (‖z‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • ((sphereCoordinates v).symm z : E4) +
        (‖z‖ ^ 2 + 4)⁻¹ • (‖z‖ ^ 2 - 4) • (v : E4) := by
  rw [standardSphereChart_eq_stereographic, stereographic'_symm_apply]
  simp only [← Submodule.coe_norm, LinearIsometryEquiv.norm_map]
  rfl



@[simp] theorem standardSphereChart_symm_zero (v : ThreeSphere) :
    (standardSphereChart v).symm 0 = -v := by
  apply Subtype.ext
  rw [standardSphereChart_symm_formula]
  norm_num [smul_smul]



noncomputable def oppositeSphereChart (v : ThreeSphere) :
    OpenPartialHomeomorph ThreeSphere StandardCapSpace :=
  sphereAntipodal.toHomeomorph.toOpenPartialHomeomorph.trans
    ((standardSphereChart v).trans
      ((LinearIsometryEquiv.neg ℝ :
        StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace).toHomeomorph.toOpenPartialHomeomorph))



@[simp] theorem oppositeSphereChart_apply (v x : ThreeSphere) :
    oppositeSphereChart v x = -(standardSphereChart v (-x)) := rfl



@[simp] theorem oppositeSphereChart_symm_apply (v : ThreeSphere) (z : StandardCapSpace) :
    (oppositeSphereChart v).symm z = -((standardSphereChart v).symm (-z)) := rfl



@[simp] theorem oppositeSphereChart_source (v : ThreeSphere) :
    (oppositeSphereChart v).source = {-v}ᶜ := by
  ext x
  have hneg (y : ThreeSphere) : sphereAntipodal y = -y := rfl
  simp [oppositeSphereChart, standardSphereChart_source, hneg, neg_eq_iff_eq_neg]



@[simp] theorem oppositeSphereChart_target (v : ThreeSphere) :
    (oppositeSphereChart v).target = univ := by
  simp [oppositeSphereChart, standardSphereChart_target]



theorem oppositeSphereChart_contMDiffOn (v : ThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (oppositeSphereChart v)
      (oppositeSphereChart v).source := by
  have hmid : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun x : ThreeSphere => standardSphereChart v (-x)) (oppositeSphereChart v).source := by
    apply (standardSphereChart_contMDiffOn v).comp contMDiff_neg_sphere.contMDiffOn
    intro x hx
    simpa only [oppositeSphereChart_source, standardSphereChart_source,
      mem_preimage, mem_compl_iff, mem_singleton_iff, neg_eq_iff_eq_neg] using hx
  exact contDiff_neg.contMDiff.comp_contMDiffOn hmid



theorem oppositeSphereChart_symm_contMDiff (v : ThreeSphere) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (oppositeSphereChart v).symm :=
  contMDiff_neg_sphere.comp ((standardSphereChart_symm_contMDiff v).comp
    contDiff_neg.contMDiff)



@[simp] theorem oppositeSphereChart_symm_zero (v : ThreeSphere) :
    (oppositeSphereChart v).symm 0 = v := by
  rw [oppositeSphereChart_symm_apply, neg_zero, standardSphereChart_symm_zero, neg_neg]



theorem sphereCharts_cover (v : ThreeSphere) :
    (standardSphereChart v).source ∪ (oppositeSphereChart v).source = univ := by
  ext x
  simp only [standardSphereChart_source, oppositeSphereChart_source,
    mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_cases hx : x = v
  · subst x
    exact Or.inr (ne_neg_of_mem_unit_sphere ℝ v)
  · exact Or.inl hx



theorem standardSphereChart_mem_opposite_iff (v : ThreeSphere) {x : ThreeSphere}
    (hx : x ∈ (standardSphereChart v).source) :
    x ∈ (oppositeSphereChart v).source ↔ standardSphereChart v x ≠ 0 := by
  rw [oppositeSphereChart_source]
  simp only [mem_compl_iff, mem_singleton_iff]
  constructor
  · intro h hzero
    have hleft := (standardSphereChart v).left_inv hx
    rw [hzero, standardSphereChart_symm_zero] at hleft
    exact h hleft.symm
  · intro h heq
    apply h
    subst x
    have hright := (standardSphereChart v).right_inv (show (0 : StandardCapSpace) ∈
      (standardSphereChart v).target by simp)
    rwa [standardSphereChart_symm_zero] at hright



theorem oppositeSphereChart_mem_standard_iff (v : ThreeSphere) {x : ThreeSphere}
    (hx : x ∈ (oppositeSphereChart v).source) :
    x ∈ (standardSphereChart v).source ↔ oppositeSphereChart v x ≠ 0 := by
  rw [standardSphereChart_source]
  simp only [mem_compl_iff, mem_singleton_iff]
  constructor
  · intro h hzero
    have hleft := (oppositeSphereChart v).left_inv hx
    rw [hzero, oppositeSphereChart_symm_zero] at hleft
    exact h hleft.symm
  · intro h heq
    apply h
    subst x
    have hright := (oppositeSphereChart v).right_inv (show (0 : StandardCapSpace) ∈
      (oppositeSphereChart v).target by simp)
    rwa [oppositeSphereChart_symm_zero] at hright

private theorem inversion_two_formula (z : StandardCapSpace) :
    EuclideanGeometry.inversion (0 : StandardCapSpace) 2 z = (4 / ‖z‖ ^ 2) • z := by
  norm_num [EuclideanGeometry.inversion, div_pow]



theorem oppositeSphereChart_symm_inversion (v : ThreeSphere) {z : StandardCapSpace}
    (hz : z ≠ 0) :
    (oppositeSphereChart v).symm (EuclideanGeometry.inversion 0 2 z) =
      (standardSphereChart v).symm z := by
  rw [oppositeSphereChart_symm_apply]
  apply Subtype.ext
  change -((standardSphereChart v).symm (-EuclideanGeometry.inversion 0 2 z) : E4) = _
  rw [standardSphereChart_symm_formula, standardSphereChart_symm_formula]
  have hn : ‖EuclideanGeometry.inversion (0 : StandardCapSpace) 2 z‖ = 4 / ‖z‖ := by
    have h := EuclideanGeometry.dist_inversion_center (0 : StandardCapSpace) z 2
    norm_num at h
    exact h
  simp only [norm_neg, map_neg, Submodule.coe_neg, smul_neg, neg_add, neg_neg]
  rw [hn, inversion_two_formula]
  simp only [map_smul, Submodule.coe_smul, ← neg_smul, smul_smul]
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hd0 : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have he0 : (4 / ‖z‖) ^ 2 + 4 ≠ 0 := by positivity
  congr 1
  · congr 1
    field_simp
    ring
  · congr 1
    field_simp
    ring



theorem oppositeSphereChart_transition (v : ThreeSphere) {x : ThreeSphere}
    (hx0 : x ∈ (standardSphereChart v).source)
    (hx1 : x ∈ (oppositeSphereChart v).source) :
    oppositeSphereChart v x = EuclideanGeometry.inversion 0 2 (standardSphereChart v x) := by
  have hz := (standardSphereChart_mem_opposite_iff v hx0).mp hx1
  have heq := oppositeSphereChart_symm_inversion v hz
  rw [(standardSphereChart v).left_inv hx0] at heq
  have hright := (oppositeSphereChart v).right_inv
    (show EuclideanGeometry.inversion 0 2 (standardSphereChart v x) ∈
      (oppositeSphereChart v).target by simp)
  rwa [heq] at hright

end PoincareConjecture.M74
