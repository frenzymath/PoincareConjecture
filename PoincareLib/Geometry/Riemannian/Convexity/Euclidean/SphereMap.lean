import PoincareLib.Geometry.Manifold.Diffeomorph.Sphere
import PoincareLib.Geometry.Manifold.LocalDiffeomorph
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.LocalInverse

/-!
# Sphere-valued maps with nonsingular ambient derivative

The differential step in the Euclidean Gauss-map argument: a smooth unit
vector field with injective derivative is a local diffeomorphism to the unit
sphere. Compactness and connectedness then give a global diffeomorphism in
dimension at least two, as in Eschenburg, Lemma 6.6, pp. 517-518.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Riemannian.Convexity

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem isLocalDiffeomorph_of_injective_mfderiv
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (E n) M] [ChartedSpace (E n) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {f : M → N} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  have hinv : ∀ x, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible := by
    intro x
    let A : E n →L[ℝ] E n := mfderiv (𝓡 n) (𝓡 n) f x
    have hbij : Function.Bijective A :=
      ⟨hinj x, LinearMap.injective_iff_surjective.mp (hinj x)⟩
    exact ⟨ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
  intro x
  let c := chartAt (E n) x
  let C : PartialDiffeomorph (𝓡 n) (𝓡 n) M (E n) ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := contMDiffOn_extChartAt
    contMDiffOn_invFun := by
      simpa [extChartAt_coe_symm, extChartAt_target, c] using
        contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x }
  have hC : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c x :=
    C.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (mem_chart_source _ _)
  have hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f ∘ c.symm) c.target :=
    hf.comp_contMDiffOn C.contMDiffOn_invFun
  have hgi : ∀ y ∈ c.target,
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y).IsInvertible := by
    intro y hy
    have hcs : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
      C.symm.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hy
    rw [mfderiv_comp y ((hf (c.symm y)).mdifferentiableAt (by simp))
      (hcs.mdifferentiableAt (by simp))]
    exact (hinv _).comp ⟨hcs.mfderivToContinuousLinearEquiv (by simp),
      hcs.mfderivToContinuousLinearEquiv_coe (by simp)⟩
  have hlocal := PoincareMT.RiemannianMetric.isLocalDiffeomorphOn_of_isInvertible_mfderiv
    c.open_target hg hgi ⟨c x, c.map_source (mem_chart_source _ _)⟩
  apply (hC.comp (𝓡 n) N hlocal).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ _)] with y hy
  simp only [Function.comp_apply, c.left_inv hy]

/-- Injectivity of the ambient differential makes a smooth sphere-valued map
a local diffeomorphism. -/
theorem isLocalDiffeomorph_sphere_of_injective_ambient_mfderiv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → Metric.sphere (0 : E (n + 1)) 1}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hinj : ∀ x, Function.Injective
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun y => (f y : E (n + 1))) x)) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  apply isLocalDiffeomorph_of_injective_mfderiv hf
  intro x
  have hcomp := mfderiv_comp x
    ((contMDiff_coe_sphere (n := n) (m := ∞) (f x)).mdifferentiableAt (by simp))
    ((hf x).mdifferentiableAt (by simp))
  apply Function.Injective.of_comp (g := mfderiv (𝓡 n) (𝓡 n) f x)
    (f := mfderiv (𝓡 n) (𝓡 (n + 1)) Subtype.val (f x))
  change Function.Injective ((mfderiv (𝓡 n) (𝓡 (n + 1)) Subtype.val (f x)).comp
    (mfderiv (𝓡 n) (𝓡 n) f x))
  rw [← hcomp]
  exact hinj x

/-- A smooth unit vector field with injective derivative on a compact connected
manifold of dimension at least two yields a diffeomorphism to the sphere. -/
def sphereDiffeomorphOfUnitMap
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (n + 2)) M] [IsManifold (𝓡 (n + 2)) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    (N : M → E ((n + 2) + 1))
    (hN : ContMDiff (𝓡 (n + 2)) (𝓡 ((n + 2) + 1)) ∞ N)
    (hunit : ∀ x, ‖N x‖ = 1)
    (hinj : ∀ x, Function.Injective
      (mfderiv (𝓡 (n + 2)) (𝓡 ((n + 2) + 1)) N x)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) M
      (Metric.sphere (0 : E ((n + 2) + 1)) 1) ∞ := by
  let : Fact (Module.finrank ℝ (E ((n + 2) + 1)) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hmem : ∀ x, N x ∈ Metric.sphere (0 : E ((n + 2) + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit
  let f : M → Metric.sphere (0 : E ((n + 2) + 1)) 1 := Set.codRestrict N _ hmem
  exact Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph f
    (isLocalDiffeomorph_sphere_of_injective_ambient_mfderiv
      (hN.codRestrict_sphere hmem) hinj)

end Poincare.Geometry.Riemannian.Convexity
