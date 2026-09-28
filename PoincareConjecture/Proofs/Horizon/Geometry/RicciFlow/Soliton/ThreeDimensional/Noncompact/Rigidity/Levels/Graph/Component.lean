import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Manifold.RegularLevel

namespace Poincare.Manifold

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (c : ℝ)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem isLocalDiffeomorph_into_level_of_ambient_immersion
    (F : N → openLevelSet f U c)
    (hF : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (openLevelIncl f U c ∘ F))
    (hinj : ∀ x, Injective
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c ∘ F) x)) :
    letI := openLevelSetChartedSpace hf U hreg n c
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hFs : ContMDiff (𝓡 n) (𝓡 n) ∞ F := fun x =>
    (contMDiffAt_into_openLevelSet_iff hf n c U hreg F x).mpr (hF x)
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hFs
  intro x
  have hcomp := mfderiv_comp x
    ((contMDiff_openLevelIncl hf U hreg n c (F x)).mdifferentiableAt (by simp))
    ((hFs x).mdifferentiableAt (by simp))
  have hFi : Injective (mfderiv (𝓡 n) (𝓡 n) F x) := by
    apply Function.Injective.of_comp
      (f := mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) (F x))
    change Injective ((mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) (F x)).comp
      (mfderiv (𝓡 n) (𝓡 n) F x))
    rw [← hcomp]
    exact hinj x
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) F x
  exact ⟨hFi, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hFi⟩

include hf hreg in

theorem range_eq_level_component_of_compact_immersion
    [T2Space M] [CompactSpace N] [ConnectedSpace N]
    (F : N → openLevelSet f U c)
    (hF : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (openLevelIncl f U c ∘ F))
    (hinj : ∀ x, Injective
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c ∘ F) x)) (x : N) :
    range F = connectedComponent (F x) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hlocal := isLocalDiffeomorph_into_level_of_ambient_immersion hf U hreg c F hF hinj
  have hcont : Continuous F := hlocal.contMDiff.continuous
  have hclosed : IsClosed (range F) := (isCompact_range hcont).isClosed
  have hclopen : IsClopen (range F) := ⟨hclosed, hlocal.isOpen_range⟩
  exact (isPreconnected_range hcont).subset_connectedComponent (mem_range_self x)
    |>.antisymm (hclopen.connectedComponent_subset (mem_range_self x))

end Poincare.Manifold
