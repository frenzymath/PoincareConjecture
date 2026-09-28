import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ N]



theorem scalarCurvature_eq_regularLevel_of_ambient_pullback
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) (g : RiemannianMetric (n + 1) M) (gN : RiemannianMetric n N)
    (DN : LeviCivitaData gN) (F : N → openLevelSet f U c)
    (hF : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (openLevelIncl f U c ∘ F))
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x), gN.inner x v w =
      g.inner (openLevelIncl f U c (F x))
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c ∘ F) x v)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c ∘ F) x w)) (x : N) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    DN.scalarCurvature x =
      (RiemannianMetric.regularLevelMetric hf U hreg c g).leviCivitaData.scalarCurvature (F x) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hFs : ContMDiff (𝓡 n) (𝓡 n) ∞ F := fun y =>
    (contMDiffAt_into_openLevelSet_iff hf n c U hreg F y).mpr (hF y)
  apply DN.scalarCurvature_eq_of_local_isometry
    (RiemannianMetric.regularLevelMetric hf U hreg c g).leviCivitaData
    isOpen_univ hFs.contMDiffOn (fun y _ v w => ?_) (mem_univ x)
  rw [RiemannianMetric.regularLevelMetric_inner, hmetric]
  have he := mfderiv_comp y
    ((contMDiff_openLevelIncl hf U hreg n c (F y)).mdifferentiableAt (by simp))
    ((hFs y).mdifferentiableAt (by simp))
  rw [he]
  rfl

end PoincareConjecture.LeviCivitaData
