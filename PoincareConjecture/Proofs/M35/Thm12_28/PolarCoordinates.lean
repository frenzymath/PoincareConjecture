import PoincareConjecture.Definitions.Ch12.StandardCap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.SMul










set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



noncomputable def spherePolarMap (q₀ : UnitTwoSphere) (x : StandardCapSpace) :
    StandardCylinderSpace :=
  if hx : x = 0 then (q₀, -1) else
    (⟨‖x‖⁻¹ • x, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩, ‖x‖ - 1)



theorem spherePolarMap_sphere (q₀ q : UnitTwoSphere) :
    spherePolarMap q₀ q.val = (q, 0) := by
  have hnorm : ‖q.val‖ = 1 := norm_eq_of_mem_sphere q
  have hq : q.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  apply Prod.ext
  · apply Subtype.ext
    simp [spherePolarMap, hq, hnorm]
  · simp [spherePolarMap, hq, hnorm]



theorem spherePolarMap_neg (q₀ : UnitTwoSphere) {x : StandardCapSpace} (hx : x ≠ 0) :
    spherePolarMap q₀ (-x) = (-(spherePolarMap q₀ x).1, (spherePolarMap q₀ x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [spherePolarMap, hx, neg_ne_zero.mpr hx]
  · simp [spherePolarMap, hx, neg_ne_zero.mpr hx]



theorem spherePolarMap_contMDiffAt (q₀ : UnitTwoSphere)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (spherePolarMap q₀) x := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let U : Opens StandardCapSpace := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hU (y : U) : y.val ≠ 0 := y.property
  have hraw : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => ‖y.val‖⁻¹ • y.val) := by
    intro y
    apply (contMDiffAt_subtype_iff (U := U)
      (f := fun z : StandardCapSpace => ‖z‖⁻¹ • z) (x := y)).mpr
    exact (((contDiffAt_norm ℝ (hU y)).inv (norm_ne_zero_iff.mpr (hU y))).smul
      contDiffAt_id).contMDiffAt
  have hnorm (y : U) : ‖y.val‖⁻¹ • y.val ∈ Metric.sphere (0 : StandardCapSpace) 1 := by
    simp [norm_smul, norm_ne_zero_iff.mpr (hU y)]
  have hdir := hraw.codRestrict_sphere (n := 2) hnorm
  have htime : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : U => ‖y.val‖ - 1) := by
    intro y
    apply (contMDiffAt_subtype_iff (U := U)
      (f := fun z : StandardCapSpace => ‖z‖ - 1) (x := y)).mpr
    exact ((contDiffAt_norm ℝ (hU y)).sub contDiffAt_const).contMDiffAt
  have hprod := hdir.prodMk htime
  have heq : (fun y : U => spherePolarMap q₀ y.val) =
      (fun y : U => (⟨‖y.val‖⁻¹ • y.val, hnorm y⟩, ‖y.val‖ - 1)) := by
    funext y
    simp only [spherePolarMap, dif_neg (hU y)]
  have hp : ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : U => spherePolarMap q₀ y.val) := heq.symm ▸ hprod
  exact (contMDiffAt_subtype_iff (U := U) (f := spherePolarMap q₀)
    (x := ⟨x, hx⟩)).mp (hp ⟨x, hx⟩)



theorem spherePolarMap_mfderiv_injective (q₀ : UnitTwoSphere)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    Function.Injective (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (spherePolarMap q₀) x) := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let r : StandardCylinderSpace → StandardCapSpace := fun p => (p.2 + 1) • p.1.val
  have hr : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ r :=
    (contMDiff_snd.add contMDiff_const).smul
      ((contMDiff_coe_sphere (n := 2) (E := StandardCapSpace)).comp contMDiff_fst)
  have hleft : r ∘ spherePolarMap q₀ =ᶠ[𝓝 x] id := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    change y ≠ 0 at hy
    simp [r, spherePolarMap, hy, smul_smul, norm_ne_zero_iff.mpr hy]
  have hd := mfderiv_comp x (hr.mdifferentiable (by simp) _)
    ((spherePolarMap_contMDiffAt q₀ hx).mdifferentiableAt (by simp))
  rw [hleft.mfderiv_eq, mfderiv_id] at hd
  apply Function.LeftInverse.injective
    (g := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) r (spherePolarMap q₀ x))
  intro v
  exact (congrArg (fun L => L v) hd).symm

end PoincareConjecture.M35
