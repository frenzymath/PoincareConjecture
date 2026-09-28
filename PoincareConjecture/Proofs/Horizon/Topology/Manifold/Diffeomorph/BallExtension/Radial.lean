import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition












noncomputable section
set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => PoincareConjecture.UnitTwoSphere
local notation "SphereModel" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 2)

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩


def sphereRadialMap (f : ℝ → S2 → S2) (x : E3) : E3 :=
  if h : x = 0 then 0 else
    ‖x‖ • (f ‖x‖ ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, norm_ne_zero_iff.mpr h]⟩ : E3)

@[simp] theorem sphereRadialMap_zero (f : ℝ → S2 → S2) :
    sphereRadialMap f 0 = 0 := by
  simp [sphereRadialMap]


@[simp] theorem norm_sphereRadialMap (f : ℝ → S2 → S2) (x : E3) :
    ‖sphereRadialMap f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sphereRadialMap, hx, norm_smul]


theorem sphereRadialMap_smul (f : ℝ → S2 → S2) (p : S2) {r : ℝ}
    (hr : 0 < r) :
    sphereRadialMap f (r • (p : E3)) = r • (f r p : E3) := by
  have hn : ‖r • (p : E3)‖ = r := by
    simp [norm_smul, abs_of_pos hr]
  have hne : r • (p : E3) ≠ 0 :=
    smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere p)
  simp only [sphereRadialMap, dif_neg hne, hn]
  congr 2
  apply Subtype.ext
  simp [smul_smul, hr.ne']


theorem sphereRadialMap_leftInverse (f g : ℝ → S2 → S2)
    (hgf : ∀ r, Function.LeftInverse (g r) (f r)) :
    Function.LeftInverse (sphereRadialMap g) (sphereRadialMap f) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let p : S2 := ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩
    have hfx : sphereRadialMap f x = ‖x‖ • (f ‖x‖ p : E3) := by
      simp [sphereRadialMap, hx, p]
    rw [hfx, sphereRadialMap_smul g _ (norm_pos_iff.mpr hx), hgf]
    simp [p, smul_smul, norm_ne_zero_iff.mpr hx]



theorem sphereRadialMap_eq_linearIsometry (f : ℝ → S2 → S2)
    (A : E3 ≃ₗᵢ[ℝ] E3) {x : E3}
    (hf : ∀ p : S2, (f ‖x‖ p : E3) = A p) :
    sphereRadialMap f x = A x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [sphereRadialMap, dif_neg hx, hf, map_smul]
    simp [smul_smul, norm_ne_zero_iff.mpr hx]


theorem contMDiffAt_sphereRadialMap (f : ℝ → S2 → S2)
    (hf : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => f z.1 z.2))
    {x : E3} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (sphereRadialMap f) x := by
  let U : Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let p : U → S2 := fun y =>
    ⟨‖(y : E3)‖⁻¹ • (y : E3), by
      simp [norm_smul, norm_ne_zero_iff.mpr y.property]⟩
  have hv : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => (y : E3)) :=
    contMDiff_subtype_val
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : U => ‖(y : E3)‖) := by
    intro y
    exact (contDiffAt_norm ℝ y.property).contMDiffAt.comp y hv.contMDiffAt
  have hp : ContMDiff (𝓡 3) (𝓡 2) ∞ p :=
    (hn.inv₀ (fun y => norm_ne_zero_iff.mpr y.property)).smul hv |>.codRestrict_sphere _
  have h : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => sphereRadialMap f y) := by
    have heq : (fun y : U => sphereRadialMap f y) =
        (fun y : U => ‖(y : E3)‖ • (f ‖(y : E3)‖ (p y) : E3)) := by
      funext y
      exact dif_neg y.property
    rw [heq]
    exact hn.smul (contMDiff_coe_sphere.comp (hf.comp (hn.prodMk hp)))
  exact (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp h.contMDiffAt


theorem contMDiff_sphereRadialMap (f : ℝ → S2 → S2)
    (hf : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => f z.1 z.2))
    (A : E3 ≃ₗᵢ[ℝ] E3) {a : ℝ} (ha : 0 < a)
    (hA : ∀ r < a, ∀ p : S2, (f r p : E3) = A p) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (sphereRadialMap f) := by
  intro x
  by_cases hx : x = 0
  · subst x
    apply A.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E3) ha] with y hy
    exact sphereRadialMap_eq_linearIsometry f A (hA ‖y‖ (by simpa using hy))
  · exact contMDiffAt_sphereRadialMap f hf hx



def sphereRadialDiffeomorph
    (f : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞)
    (hf : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => f z.1 z.2))
    (hi : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => (f z.1).symm z.2))
    (A : E3 ≃ₗᵢ[ℝ] E3) {a : ℝ} (ha : 0 < a)
    (hA : ∀ r < a, ∀ p : S2, (f r p : E3) = A p) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun := sphereRadialMap (fun r => f r)
  invFun := sphereRadialMap (fun r => (f r).symm)
  left_inv := sphereRadialMap_leftInverse _ _ (fun r => (f r).left_inv)
  right_inv := sphereRadialMap_leftInverse _ _ (fun r => (f r).right_inv)
  contMDiff_toFun := contMDiff_sphereRadialMap _ hf A ha hA
  contMDiff_invFun := contMDiff_sphereRadialMap (fun r => (f r).symm) hi A.symm ha (by
    intro r hr p
    apply A.injective
    rw [A.apply_symm_apply, ← hA r hr ((f r).symm p)]
    simp)


theorem image_closedBall_eq_of_norm_eq (e : E3 ≃ E3)
    (he : ∀ x, ‖e x‖ = ‖x‖) (r : ℝ) :
    e '' Metric.closedBall 0 r = Metric.closedBall 0 r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, he] using hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have hnorm : ‖e.symm y‖ = ‖y‖ := by simpa using (he (e.symm y)).symm
    simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using hy



theorem exists_sphere_diffeomorph_extension_of_isotopy
    (d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞)
    (A : E3 ≃ₗᵢ[ℝ] E3)
    (f : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞)
    (hf : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => f z.1 z.2))
    (hzero : ∀ p : S2, (f 0 p : E3) = A p)
    (hone : ∀ p : S2, f 1 p = d p) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' Metric.closedBall 0 1 = Metric.closedBall 0 1 ∧
      ∀ (p : S2) (r : ℝ), 1 / 2 < r → F (r • (p : E3)) = r • (d p : E3) := by
  let τ : ℝ → ℝ := fun r => Real.smoothTransition (4 * r - 1)
  let g : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞ := fun r => f (τ r)
  have hτ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ τ :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contMDiff
  have hg : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => g z.1 z.2) :=
    hf.comp ((hτ.comp contMDiff_fst).prodMk contMDiff_snd)
  have hgi : ContMDiff SphereModel (𝓡 2) ∞ (fun z : ℝ × S2 => (g z.1).symm z.2) :=
    contMDiff_diffeomorph_family_symm g hg
  have hA : ∀ r < (1 / 4 : ℝ), ∀ p : S2, (g r p : E3) = A p := by
    intro r hr p
    have ht : τ r = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simpa only [g, ht] using hzero p
  let F := sphereRadialDiffeomorph g hg hgi A (by norm_num : (0 : ℝ) < 1 / 4) hA
  refine ⟨F, image_closedBall_eq_of_norm_eq F.toEquiv (norm_sphereRadialMap _) 1, ?_⟩
  intro p r hr
  change sphereRadialMap (fun r => g r) (r • (p : E3)) = _
  rw [sphereRadialMap_smul _ p (by linarith)]
  have ht : τ r = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  simp only [g, ht, hone]

end Poincare.Manifold
