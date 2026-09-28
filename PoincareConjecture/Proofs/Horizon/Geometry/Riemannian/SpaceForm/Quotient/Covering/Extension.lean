import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Rigidity


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem exists_ambient_motion_of_local_round_isometry
    {k : UnitSphere n → UnitSphere n} {U : Set (UnitSphere n)}
    (hU : IsOpen U) (hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U)
    (hkm : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      (roundSphereMetric n).inner x v w = (roundSphereMetric n).inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w))
    {p : UnitSphere n} (hp : p ∈ U) :
    ∃ L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      sphereMotion L =ᶠ[𝓝 p] k := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) := by
    unfold TangentSpace
    infer_instance
  have hbij := (roundSphereMetric n).mfderiv_bijective_of_pullback_eq
    (roundSphereMetric n) p (fun v w => (hkm p hp v w).symm)
  let A : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) (k p) :=
    (LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) k p).toLinearMap
      hbij).toContinuousLinearEquiv
  obtain ⟨L, hLp, hLd⟩ := exists_ambient_sphere_motion_firstOrder p (k p) A
    (fun v w => (hkm p hp v w).symm)
  refine ⟨L, PoincareConjecture.SpaceForm.local_isometry_germ_ext
    (roundSphereMetric n) (roundSphereMetric n) hU
    (sphereMotion L).contMDiff.contMDiffOn hk
    (fun x _ v w => (sphereMotion_inner L x v w).symm) hkm hp hLp ?_⟩
  ext v
  exact hLd v



theorem extend_inverse_round_isometry
    (g : RiemannianMetric n M) {k : UnitSphere n → M} {U : Set (UnitSphere n)}
    (hU : IsOpen U) (hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U)
    (hkm : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      (roundSphereMetric n).inner x v w = g.inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w))
    {p : UnitSphere n} (hp : p ∈ U)
    (F : OpenPartialHomeomorph M (UnitSphere n)) (hpF : k p ∈ F.source)
    (hF : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target)
    (hFm : ∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = (roundSphereMetric n).inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {r : ℝ} (hball : Metric.ball (F (k p)) r ⊆ F.target) :
    ∃ f : UnitSphere n → M,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball p r) ∧
      (∀ x ∈ Metric.ball p r, ∀ v w : TangentSpace (𝓡 n) x,
        (roundSphereMetric n).inner x v w = g.inner (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)) ∧
      f =ᶠ[𝓝 p] k := by
  let W := U ∩ k ⁻¹' F.source
  have hW : IsOpen W := hk.continuousOn.isOpen_inter_preimage hU F.open_source
  have hpW : p ∈ W := ⟨hp, hpF⟩
  have hFk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (F ∘ k) W :=
    hF.comp (hk.mono inter_subset_left) (fun _ hx => hx.2)
  have hFkm (x : UnitSphere n) (hx : x ∈ W) (v w : TangentSpace (𝓡 n) x) :
      (roundSphereMetric n).inner x v w = (roundSphereMetric n).inner ((F ∘ k) x)
        (mfderiv (𝓡 n) (𝓡 n) (F ∘ k) x v)
        (mfderiv (𝓡 n) (𝓡 n) (F ∘ k) x w) := by
    rw [mfderiv_comp x
      ((hF.contMDiffAt (F.open_source.mem_nhds hx.2)).mdifferentiableAt (by simp))
      ((hk.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))]
    exact (hkm x hx.1 v w).trans (hFm (k x) hx.2 _ _)
  obtain ⟨L, hL⟩ := exists_ambient_motion_of_local_round_isometry hW hFk hFkm hpW
  have hLp : sphereMotion L p = F (k p) := hL.self_of_nhds
  have hmap : MapsTo (sphereMotion L) (Metric.ball p r) F.target := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, ← hLp, (isometry_sphereMotion L).dist_eq]
    exact hx
  let f : UnitSphere n → M := F.symm ∘ sphereMotion L
  have hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball p r) :=
    hFi.comp (sphereMotion L).contMDiff.contMDiffOn hmap
  refine ⟨f, hf, ?_, ?_⟩
  · intro x hx v w
    have hInv := inverse_local_isometry_inner g (roundSphereMetric n) F hF hFi hFm
      (sphereMotion L x) (hmap hx)
      (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x v)
      (mfderiv (𝓡 n) (𝓡 n) (sphereMotion L) x w)
    change (roundSphereMetric n).inner x v w = g.inner (F.symm (sphereMotion L x))
      (mfderiv (𝓡 n) (𝓡 n) (F.symm ∘ sphereMotion L) x v)
      (mfderiv (𝓡 n) (𝓡 n) (F.symm ∘ sphereMotion L) x w)
    rw [mfderiv_comp x
      ((hFi.contMDiffAt (F.open_target.mem_nhds (hmap hx))).mdifferentiableAt (by simp))
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    exact (sphereMotion_inner L x v w).symm.trans hInv
  · filter_upwards [hL, hW.mem_nhds hpW] with x hx hxW
    change F.symm (sphereMotion L x) = k x
    rw [hx]
    exact F.left_inv hxW.2

end Poincare.Geometry.Riemannian.SpaceForm
