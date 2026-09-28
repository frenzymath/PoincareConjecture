import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Rigidity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.SphereMotions








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



theorem sphere_motion_comp_local_isometry
    (g : RiemannianMetric n M) {f : M → UnitSphere n} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hfmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = (roundSphereMetric n).inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (O : Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞)
    (hOmetric : ∀ x u v, (roundSphereMetric n).inner (O x)
      (mfderiv (𝓡 n) (𝓡 n) O x u) (mfderiv (𝓡 n) (𝓡 n) O x v) =
        (roundSphereMetric n).inner x u v) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (O ∘ f) U ∧
      ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
        g.inner x v w = (roundSphereMetric n).inner ((O ∘ f) x)
          (mfderiv (𝓡 n) (𝓡 n) (O ∘ f) x v)
          (mfderiv (𝓡 n) (𝓡 n) (O ∘ f) x w) := by
  refine ⟨(O.contMDiff.contMDiffOn (s := univ)).comp hf (fun _ _ => mem_univ _), ?_⟩
  intro x hx v w
  rw [mfderiv_comp x (O.contMDiffAt.mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
  exact (hfmetric x hx v w).trans (hOmetric (f x) _ _).symm



theorem exists_sphere_motion_of_local_isometries [T2Space M] [CompactSpace M]
    (g : RiemannianMetric n M) {f k : M → UnitSphere n} {U : Set M}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U)
    (hfmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = (roundSphereMetric n).inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (hkmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = (roundSphereMetric n).inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w))
    {p : M} (hp : p ∈ U) :
    ∃ O : Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞,
      (∀ x u v, (roundSphereMetric n).inner (O x)
        (mfderiv (𝓡 n) (𝓡 n) O x u) (mfderiv (𝓡 n) (𝓡 n) O x v) =
          (roundSphereMetric n).inner x u v) ∧
      (O ∘ f) =ᶠ[𝓝 p] k := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) := by
    unfold TangentSpace
    infer_instance
  have hfbij := g.mfderiv_bijective_of_pullback_eq (roundSphereMetric n) p
    (fun v w => (hfmetric p hp v w).symm)
  have hkbij := g.mfderiv_bijective_of_pullback_eq (roundSphereMetric n) p
    (fun v w => (hkmetric p hp v w).symm)
  let Lf : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f p).toLinearMap hfbij).toContinuousLinearEquiv
  let Lk : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) k p).toLinearMap hkbij).toContinuousLinearEquiv
  let A : TangentSpace (𝓡 n) (f p) ≃L[ℝ] TangentSpace (𝓡 n) (k p) := Lf.symm.trans Lk
  have hA (u v : TangentSpace (𝓡 n) (f p)) :
      (roundSphereMetric n).inner (k p) (A u) (A v) =
        (roundSphereMetric n).inner (f p) u v := by
    calc
      _ = g.inner p (Lf.symm u) (Lf.symm v) := (hkmetric p hp _ _).symm
      _ = (roundSphereMetric n).inner (f p)
          (Lf (Lf.symm u)) (Lf (Lf.symm v)) := hfmetric p hp _ _
      _ = _ := by rw [Lf.apply_symm_apply, Lf.apply_symm_apply]
  obtain ⟨O, hOp, hOd, hOmetric⟩ := exists_sphere_motion (f p) (k p) A hA
  obtain ⟨hOf, hOfmetric⟩ := sphere_motion_comp_local_isometry g hU hf hfmetric O hOmetric
  refine ⟨O, hOmetric, PoincareConjecture.SpaceForm.local_isometry_germ_ext g
    (roundSphereMetric n) hU hOf hk hOfmetric hkmetric hp hOp ?_⟩
  rw [mfderiv_comp p (O.contMDiffAt.mdifferentiableAt (by simp))
    ((hf.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))]
  ext v
  change mfderiv (𝓡 n) (𝓡 n) O (f p) (Lf v) = Lk v
  rw [hOd]
  change Lk (Lf.symm (Lf v)) = Lk v
  rw [Lf.symm_apply_apply]

end Poincare.Geometry.Riemannian.SpaceForm
