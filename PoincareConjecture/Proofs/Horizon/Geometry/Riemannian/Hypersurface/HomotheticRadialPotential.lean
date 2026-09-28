import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hypersurface.RadialPotential
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.SMul

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem normalized_homothety_isLocalDiffeomorph
    (g : RiemannianMetric n M) {c : ℝ} (hc : 0 < c)
    {F : M → EuclideanSpace ℝ (Fin n)} (hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) =
        c * g.inner x v w) :
    let J : M → EuclideanSpace ℝ (Fin n) := fun x => (Real.sqrt c)⁻¹ • F x
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ J ∧
      ∀ x (v w : TangentSpace (𝓡 n) x),
        g.inner x v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) J x v)
          (mfderiv (𝓡 n) (𝓡 n) J x w) := by
  let J : M → EuclideanSpace ℝ (Fin n) := fun x => (Real.sqrt c)⁻¹ • F x
  have hJ : ContMDiff (𝓡 n) (𝓡 n) ∞ J :=
    (contMDiff_const (I' := 𝓘(ℝ, ℝ)) (c := (Real.sqrt c)⁻¹)).smul hF
  have hdJ (x : M) : mfderiv (𝓡 n) (𝓡 n) J x =
      (Real.sqrt c)⁻¹ • mfderiv (𝓡 n) (𝓡 n) F x :=
    const_smul_mfderiv (hF.mdifferentiable (by simp) x) _
  have hm (x : M) (v w : TangentSpace (𝓡 n) x) :
      g.inner x v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) J x v)
        (mfderiv (𝓡 n) (𝓡 n) J x w) := by
    have hdv (a : TangentSpace (𝓡 n) x) :
        (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) J x a) =
          (Real.sqrt c)⁻¹ • (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) F x a) := by
      exact congrArg (fun L => (show EuclideanSpace ℝ (Fin n) from L a)) (hdJ x)
    have he := congrArg₂ (inner ℝ) (hdv v) (hdv w)
    rw [real_inner_smul_left, real_inner_smul_right, hmetric] at he
    have hs : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
    calc
      g.inner x v w = 1 * g.inner x v w := by ring
      _ = ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c) * g.inner x v w := by rw [hs]
      _ = (Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * (c * g.inner x v w)) := by ring
      _ = _ := he.symm
  refine ⟨Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hJ ?_, hm⟩
  intro x
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) J x
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hne
    have hp := g.pos x v hne
    have hh := congrArg (fun a : EuclideanSpace ℝ (Fin n) => inner ℝ a a) hv
    have hzero : inner ℝ (L v) (L v) = 0 := hh.trans (by simp)
    have hz : g.inner x v v = 0 := (hm x v v).trans hzero
    linarith
  change Function.Bijective L
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem exists_unit_umbilic_of_homothetic_radial_potential
    {m : ℕ} {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) S] [IsManifold (𝓡 m) ∞ S]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {c : ℝ} (hc : 0 < c)
    {F : M → EuclideanSpace ℝ (Fin n)} (hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) =
        c * g.inner x v w)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hess : ∀ x (v w : TangentSpace (𝓡 n) x), D.hessian u x v w = g.inner x v w)
    {b : S → M} (hb : ContMDiff (𝓡 m) (𝓡 n) ∞ b)
    (hbimm : ∀ z, Function.Injective (mfderiv (𝓡 m) (𝓡 n) b z))
    (hunit : ∀ z, g.inner (b z) (D.gradient u (b z)) (D.gradient u (b z)) = 1) :
    ∃ f N : S → EuclideanSpace ℝ (Fin n),
      (∀ z, f z = (Real.sqrt c)⁻¹ • F (b z)) ∧
      ContMDiff (𝓡 m) (𝓡 n) ∞ f ∧ ContMDiff (𝓡 m) (𝓡 n) ∞ N ∧
      (∀ z, Function.Injective (mfderiv (𝓡 m) (𝓡 n) f z)) ∧
      (∀ z, ‖N z‖ = 1) ∧
      (∀ z, mfderiv (𝓡 m) (𝓡 n) N z = mfderiv (𝓡 m) (𝓡 n) f z) ∧
      ∀ z (v w : TangentSpace (𝓡 m) z),
        g.inner (b z) (mfderiv (𝓡 m) (𝓡 n) b z v) (mfderiv (𝓡 m) (𝓡 n) b z w) =
          inner ℝ (mfderiv (𝓡 m) (𝓡 n) f z v) (mfderiv (𝓡 m) (𝓡 n) f z w) := by
  let J : M → EuclideanSpace ℝ (Fin n) := fun x => (Real.sqrt c)⁻¹ • F x
  obtain ⟨hJ, hJmetric⟩ := normalized_homothety_isLocalDiffeomorph g hc hF hmetric
  obtain ⟨N, hN, _, hNunit, hNderiv⟩ :=
    exists_unit_umbilic_of_radial_potential D hJ hJmetric hu hess hb hunit
  refine ⟨J ∘ b, N, fun _ => rfl, hJ.contMDiff.comp hb, hN, ?_, hNunit, hNderiv, ?_⟩
  · intro z
    rw [mfderiv_comp z (hJ.mdifferentiable (by simp) (b z)) (hb.mdifferentiable (by simp) z)]
    exact ((hJ (b z)).mfderivToContinuousLinearEquiv (by simp)).injective.comp (hbimm z)
  · intro z v w
    rw [mfderiv_comp z (hJ.mdifferentiable (by simp) (b z)) (hb.mdifferentiable (by simp) z)]
    exact hJmetric (b z) _ _

end Poincare.Geometry.Riemannian.Hypersurface
