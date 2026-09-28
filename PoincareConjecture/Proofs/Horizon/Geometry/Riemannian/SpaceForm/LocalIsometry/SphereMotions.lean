import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture
open scoped ContDiff Manifold Bundle Topology InnerProductSpace

namespace Poincare.Geometry.Riemannian.SpaceForm

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

private def sphereInclusionDeriv {n : ℕ} (p : UnitSphere n) :
    TangentSpace (𝓡 n) p →L[ℝ] E n :=
  mfderiv (𝓡 n) (𝓡 (n + 1)) ((↑) : UnitSphere n → E n) p

private theorem sphereInclusionDeriv_range {n : ℕ} (p : UnitSphere n) :
    (sphereInclusionDeriv p).range = (ℝ ∙ (p : E n))ᗮ := by
  let : Fact (Module.finrank ℝ (E n) = n + 1) := ⟨by simp [E]⟩
  exact range_mvfderiv_subtypeVal p

private theorem sphereInclusionDeriv_injective {n : ℕ} (p : UnitSphere n) :
    Function.Injective (sphereInclusionDeriv p) := by
  let : Fact (Module.finrank ℝ (E n) = n + 1) := ⟨by simp [E]⟩
  exact injective_mvfderiv_subtypeVal_sphere p

private def sphereTangentEquiv {n : ℕ} (p : UnitSphere n) :
    TangentSpace (𝓡 n) p ≃L[ℝ] (ℝ ∙ (p : E n))ᗮ := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) := by
    unfold TangentSpace
    infer_instance
  let L := (sphereInclusionDeriv p).toLinearMap
  have hmem (v : TangentSpace (𝓡 n) p) : L v ∈ (ℝ ∙ (p : E n))ᗮ := by
    rw [← sphereInclusionDeriv_range]
    exact ⟨v, rfl⟩
  let T := L.codRestrict (ℝ ∙ (p : E n))ᗮ hmem
  have hbij : Function.Bijective T := by
    constructor
    · intro u v huv
      exact sphereInclusionDeriv_injective p (congrArg Subtype.val huv)
    · rintro ⟨v, hv⟩
      rw [← sphereInclusionDeriv_range] at hv
      obtain ⟨w, hw⟩ := hv
      exact ⟨w, Subtype.ext hw⟩
  exact (LinearEquiv.ofBijective T hbij).toContinuousLinearEquiv

private theorem sphereTangentEquiv_coe {n : ℕ} (p : UnitSphere n)
    (v : TangentSpace (𝓡 n) p) :
    (sphereTangentEquiv p v : E n) = sphereInclusionDeriv p v := rfl

private theorem sphere_norm {n : ℕ} (p : UnitSphere n) : ‖(p : E n)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using p.property

private theorem sphere_inner_self {n : ℕ} (p : UnitSphere n) :
    inner ℝ (p : E n) (p : E n) = 1 := by
  rw [real_inner_self_eq_norm_sq, sphere_norm, one_pow]

private theorem sphere_normal_tangent {n : ℕ} (p : UnitSphere n)
    (v : TangentSpace (𝓡 n) p) :
    inner ℝ (p : E n) (sphereInclusionDeriv p v) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← sphereInclusionDeriv_range]
  exact ⟨v, rfl⟩

private theorem sphere_tangent_normal {n : ℕ} (p : UnitSphere n)
    (v : TangentSpace (𝓡 n) p) :
    inner ℝ (sphereInclusionDeriv p v) (p : E n) = 0 := by
  rw [real_inner_comm (p : E n) (sphereInclusionDeriv p v)]
  exact sphere_normal_tangent p v

theorem exists_ambient_sphere_motion {n : ℕ} (p q : UnitSphere n)
    (A : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hA : ∀ u v, (roundSphereMetric n).inner q (A u) (A v) =
      (roundSphereMetric n).inner p u v) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n, L (p : E n) = (q : E n) ∧
      ∀ v, L (mfderiv (𝓡 n) (𝓡 (n + 1)) ((↑) : UnitSphere n → E n) p v) =
        mfderiv (𝓡 n) (𝓡 (n + 1)) ((↑) : UnitSphere n → E n) q (A v) := by
  let P : E n →L[ℝ] TangentSpace (𝓡 n) p :=
    (sphereTangentEquiv p).symm.toContinuousLinearMap.comp
      (ℝ ∙ (p : E n))ᗮ.orthogonalProjectionOnto
  have hP (x : E n) : sphereInclusionDeriv p (P x) =
      ((ℝ ∙ (p : E n))ᗮ.orthogonalProjectionOnto x : E n) := by
    change (sphereTangentEquiv p ((sphereTangentEquiv p).symm
      ((ℝ ∙ (p : E n))ᗮ.orthogonalProjectionOnto x)) : E n) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hsplit (x : E n) : inner ℝ (p : E n) x • (p : E n) +
      sphereInclusionDeriv p (P x) = x := by
    rw [hP, ← Submodule.starProjection_unit_singleton ℝ (sphere_norm p)]
    exact (ℝ ∙ (p : E n)).starProjection_add_starProjection_orthogonal x
  let T : E n →ₗ[ℝ] E n :=
    (innerSL ℝ (p : E n)).toLinearMap.smulRight (q : E n) +
      (sphereInclusionDeriv q).toLinearMap.comp (A.toLinearMap.comp P.toLinearMap)
  have hT (x : E n) : T x = inner ℝ (p : E n) x • (q : E n) +
      sphereInclusionDeriv q (A (P x)) := rfl
  have hTinner (x y : E n) : inner ℝ (T x) (T y) = inner ℝ x y := by
    have hxy : inner ℝ x y = inner ℝ (p : E n) x * inner ℝ (p : E n) y +
        inner ℝ (sphereInclusionDeriv p (P x)) (sphereInclusionDeriv p (P y)) := by
      conv_lhs => rw [← hsplit x, ← hsplit y]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, sphere_inner_self, sphere_normal_tangent,
        sphere_tangent_normal, mul_one, mul_zero, add_zero]
      ring
    rw [hT, hT, hxy]
    have hAt := hA (P x) (P y)
    change inner ℝ (sphereInclusionDeriv q (A (P x)))
        (sphereInclusionDeriv q (A (P y))) =
      inner ℝ (sphereInclusionDeriv p (P x)) (sphereInclusionDeriv p (P y)) at hAt
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, sphere_inner_self, sphere_normal_tangent,
      sphere_tangent_normal, mul_one, mul_zero, add_zero, hAt]
    ring
  let Li := T.isometryOfInner hTinner
  have hsurj : Function.Surjective Li :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp Li.injective
  let L := LinearIsometryEquiv.ofSurjective Li hsurj
  have hLp : L (p : E n) = (q : E n) := by
    change T (p : E n) = (q : E n)
    rw [hT, sphere_inner_self]
    have hPp : P (p : E n) = 0 := by
      simp [P, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    rw [hPp, map_zero, map_zero, one_smul, add_zero]
  refine ⟨L, hLp, ?_⟩
  intro v
  have hPv : P (sphereInclusionDeriv p v) = v := by
    apply sphereInclusionDeriv_injective p
    rw [hP]
    exact congrArg Subtype.val
      ((ℝ ∙ (p : E n))ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨sphereInclusionDeriv p v, by
          rw [← sphereInclusionDeriv_range]; exact ⟨v, rfl⟩⟩)
  change T (sphereInclusionDeriv p v) = _
  rw [hT, sphere_normal_tangent, zero_smul, zero_add, hPv]
  rfl

def sphereMotion {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) :
    Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞ := by
  let : Fact (Module.finrank ℝ (E n) = n + 1) := ⟨by simp [E]⟩
  have hL (p : UnitSphere n) : L (p : E n) ∈ UnitSphere n := by
    simpa only [Metric.mem_sphere, dist_zero_right, L.norm_map] using sphere_norm p
  have hLi (p : UnitSphere n) : L.symm (p : E n) ∈ UnitSphere n := by
    simpa only [Metric.mem_sphere, dist_zero_right, L.symm.norm_map] using sphere_norm p
  exact {
    toEquiv := {
      toFun := fun p => ⟨L (p : E n), hL p⟩
      invFun := fun p => ⟨L.symm (p : E n), hLi p⟩
      left_inv := fun p => Subtype.ext (L.symm_apply_apply (p : E n))
      right_inv := fun p => Subtype.ext (L.apply_symm_apply (p : E n)) }
    contMDiff_toFun :=
      (L.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere hL
    contMDiff_invFun :=
      (L.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
        contMDiff_coe_sphere).codRestrict_sphere hLi }

@[simp] theorem sphereMotion_coe {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (x : UnitSphere n) :
    (sphereMotion L x : E n) = L (x : E n) := rfl

private theorem sphereMotion_deriv {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (x : UnitSphere n)
    (v : TangentSpace (𝓡 n) x) :
    sphereInclusionDeriv (sphereMotion L x) (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x v) =
      L (sphereInclusionDeriv x v) := by
  let : Fact (Module.finrank ℝ (E n) = n + 1) := ⟨by simp [E]⟩
  let ι : UnitSphere n → E n := (↑)
  have hι : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ ι := contMDiff_coe_sphere
  have hL : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ L :=
    L.toContinuousLinearEquiv.contDiff.contMDiff
  have hcomp := mfderiv_comp x
    (hι.contMDiffAt.mdifferentiableAt (by simp))
    ((sphereMotion L).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have heq : ι ∘ sphereMotion L = L ∘ ι := rfl
  rw [heq, mfderiv_comp x (hL.contMDiffAt.mdifferentiableAt (by simp))
    (hι.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hcomp
  have hder : fderiv ℝ L (x : E n) = L.toContinuousLinearEquiv.toContinuousLinearMap :=
    L.toContinuousLinearEquiv.fderiv
  rw [hder] at hcomp
  exact (congrArg (fun T => T v) hcomp).symm

theorem sphereMotion_inner {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) (x : UnitSphere n)
    (u v : TangentSpace (𝓡 n) x) :
    (roundSphereMetric n).inner (sphereMotion L x)
      (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x u)
      (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x v) =
        (roundSphereMetric n).inner x u v := by
  change inner ℝ
    (sphereInclusionDeriv (sphereMotion L x) (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x u))
    (sphereInclusionDeriv (sphereMotion L x) (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x v)) =
      inner ℝ (sphereInclusionDeriv x u) (sphereInclusionDeriv x v)
  rw [sphereMotion_deriv, sphereMotion_deriv, L.inner_map_map]

theorem exists_ambient_sphere_motion_firstOrder {n : ℕ} (x y : UnitSphere n)
    (A : TangentSpace (𝓡 n) x ≃L[ℝ] TangentSpace (𝓡 n) y)
    (hA : ∀ u v, (roundSphereMetric n).inner y (A u) (A v) =
      (roundSphereMetric n).inner x u v) :
    ∃ L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)),
      sphereMotion L x = y ∧
      ∀ v, mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x v = A v := by
  obtain ⟨L, hLx, hLA⟩ := exists_ambient_sphere_motion x y A hA
  have hpos : sphereMotion L x = y := Subtype.ext hLx
  refine ⟨L, hpos, ?_⟩
  intro v
  have he := sphereMotion_deriv L x v
  change ∀ v, L (sphereInclusionDeriv x v) = sphereInclusionDeriv y (A v) at hLA
  rw [hLA] at he
  erw [hpos] at he
  exact sphereInclusionDeriv_injective y he

theorem exists_sphere_motion {n : ℕ} (p q : UnitSphere n)
    (A : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hA : ∀ u v, (roundSphereMetric n).inner q (A u) (A v) =
      (roundSphereMetric n).inner p u v) :
    ∃ F : Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞,
      F p = q ∧ (∀ v, mfderiv (𝓡 n) (𝓡 n) F p v = A v) ∧
      ∀ x u v, (roundSphereMetric n).inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x u) (mfderiv (𝓡 n) (𝓡 n) F x v) =
          (roundSphereMetric n).inner x u v := by
  obtain ⟨L, hLp, hLA⟩ := exists_ambient_sphere_motion p q A hA
  have hp : sphereMotion L p = q := Subtype.ext hLp
  refine ⟨sphereMotion L, hp, ?_, sphereMotion_inner L⟩
  intro v
  have he := sphereMotion_deriv L p v
  change ∀ v, L (sphereInclusionDeriv p v) = sphereInclusionDeriv q (A v) at hLA
  rw [hLA] at he
  erw [hp] at he
  exact sphereInclusionDeriv_injective q he

end Poincare.Geometry.Riemannian.SpaceForm
