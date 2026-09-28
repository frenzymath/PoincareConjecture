import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph
import PoincareConjecture.Proofs.M11.SpatialCalculus
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def spatialChartDomain (p : M) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨(chartAt (EuclideanSpace ℝ (Fin n)) p).target,
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target⟩

noncomputable def spatialChartInverse (p : M) (x : spatialChartDomain (n := n) p) : M :=
  (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x.val

omit [IsManifold (𝓡 n) ∞ M] in
theorem spatialChartInverse_openEmbedding (p : M) :
    Topology.IsOpenEmbedding (spatialChartInverse (n := n) p) :=
  (chartAt (EuclideanSpace ℝ (Fin n)) p).symm.isOpenEmbedding_restrict

theorem spatialChartInverse_smooth (p : M) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (spatialChartInverse (n := n) p) := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_chart_symm.comp contMDiff_subtype_val.contMDiffOn (fun x _ ↦ x.property)

theorem spatialChart_symm_localDiffeomorphAt (p : M) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  exact ⟨{
    toPartialEquiv := c.symm.toPartialEquiv
    open_source := c.open_target
    open_target := c.open_source
    contMDiffOn_toFun := contMDiffOn_chart_symm
    contMDiffOn_invFun := contMDiffOn_chart
  }, hx, fun _ _ ↦ rfl⟩

theorem spatialChartInverse_localDiffeomorph (p : M) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (spatialChartInverse (n := n) p) := by
  intro x
  exact IsLocalDiffeomorphAt.comp (I := 𝓡 n) (J := 𝓡 n) (K := 𝓡 n) (P := M) (n := ∞)
    (openSubset_localDiffeomorph (J := 𝓡 n) (spatialChartDomain p) x)
    (spatialChart_symm_localDiffeomorphAt p x.val x.property)

noncomputable def spatialChartTangentEquiv (p : M) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      TangentSpace (𝓡 n) ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm x) :=
  (spatialChart_symm_localDiffeomorphAt p x hx).mfderivToContinuousLinearEquiv (by simp)

theorem spatialChartInverse_mfderiv (p : M) (x : spatialChartDomain (n := n) p)
    (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse p) x v =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x.val v := by
  change mfderiv (𝓡 n) (𝓡 n)
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ∘ Subtype.val) x v = _
  rw [mfderiv_comp_apply x
    ((spatialChart_symm_localDiffeomorphAt p x.val x.property).mdifferentiableAt (by simp))
    (contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)), mfderiv_openSubtype_val]
  rfl

theorem spatialChart_tangent_smooth (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        (⟨(chartAt (EuclideanSpace ℝ (Fin n)) p).symm x,
          mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x v⟩ :
          TangentBundle (𝓡 n) M)) (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target := contMDiffOn_chart_symm
  have ht := hs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    c.open_target.uniqueMDiffOn
  have hv : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (⟨x, v⟩ : TangentBundle (𝓡 n) _)) := by
    intro x
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  apply (ht.comp hv.contMDiffOn (fun _ hx ↦ hx)).congr
  intro x hx
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    change mfderiv (𝓡 n) (𝓡 n) c.symm x v =
      mfderivWithin (𝓡 n) (𝓡 n) c.symm c.target x v
    rw [mfderivWithin_of_isOpen c.open_target hx]

end PoincareConjecture.Proofs.M11
