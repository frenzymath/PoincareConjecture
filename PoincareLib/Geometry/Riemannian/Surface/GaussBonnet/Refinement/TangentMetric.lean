import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.MeshTransport
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# Constant tangent metrics for coordinate vertex fans

Freeze the chart pullback metric at one point. Its globally defined planar
metric measures exactly the actual surface corner angles based at that point,
even when an auxiliary planar subdivision extends beyond the chart source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareMT.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

/-- The constant planar metric given by the chart differential at one point. -/
noncomputable def coordinateTangentMetric
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (q : Plane) (hq : q ∈ F.source) : RiemannianMetric 2 Plane :=
  RiemannianMetric.ofEuclideanCoefficients (fun _ => g.pullbackCoefficients F q)
    contDiff_const
    (fun _ v w => g.symm (F q) _ _)
    (by
      intro _ v hv
      apply g.pos (F q)
      have hD : F.MDifferentiable (𝓡 2) (𝓡 2) :=
        ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
      intro hzero
      apply hv
      apply hD.mfderiv_injective hq
      dsimp only [TangentSpace] at hzero ⊢
      exact hzero.trans (map_zero (mfderiv (𝓡 2) (𝓡 2) F q)).symm)

@[simp] theorem coordinateTangentMetric_inner
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (q : Plane) (hq : q ∈ F.source) (z : Plane) (v w : TangentSpace (𝓡 2) z) :
    (coordinateTangentMetric g F hF hFi q hq).inner z v w =
      g.inner (F q) (mfderiv (𝓡 2) (𝓡 2) F q v)
        (mfderiv (𝓡 2) (𝓡 2) F q w) := rfl

/-- Coordinate sides for the identity chart have their affine velocities. -/
theorem coordinateTriangleVelocity_refl
    (b : AffineBasis (Fin 3) ℝ Plane) (i j : Fin 3) :
    coordinateTriangleVelocity (OpenPartialHomeomorph.refl Plane) b i j = b j - b i := by
  rw [coordinateTriangleVelocity_eq_differential _ b contMDiffOn_id (by simp)]
  dsimp only [TangentSpace]
  change (mfderiv (𝓡 2) (𝓡 2) id (b i)) (b j - b i) = _
  rw [mfderiv_id]
  rfl

/-- Freezing the metric preserves each actual corner based at the chosen point. -/
theorem coordinateTriangleAngle_eq_tangentMetric
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (q : Plane) (hq : q ∈ F.source)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hb : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3) (hi : b i = q) :
    coordinateTriangleAngle g F b i =
      coordinateTriangleAngle (coordinateTangentMetric g F hF hFi q hq)
        (OpenPartialHomeomorph.refl Plane) b i := by
  subst q
  simp only [coordinateTriangleAngle,
    coordinateTriangleVelocity_eq_differential F b hF hb,
    coordinateTriangleVelocity_refl, RiemannianMetric.cornerAngle,
    coordinateTangentMetric_inner, map_smul, smul_apply]

/-- The complete contribution at a sourced mesh vertex is measured by the
constant tangent metric on the plane. -/
theorem meshVertexAngleContribution_eq_tangentMetric
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (q : Plane) (hq : q ∈ F.source) (M : TriangleMesh)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F M (F q) =
      meshVertexAngleContribution (coordinateTangentMetric g F hF hFi q hq)
        (OpenPartialHomeomorph.refl Plane) M q := by
  classical
  unfold meshVertexAngleContribution
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  have hb := (meshTriangleBasis_subset_support M t).trans hM
  have hi : meshTriangleBasis M t i ∈ F.source :=
    hb (subset_convexHull ℝ _ (mem_range_self i))
  have heq : F (meshTriangleBasis M t i) = F q ↔ meshTriangleBasis M t i = q :=
    ⟨F.injOn hi hq, congrArg F⟩
  simp only [OpenPartialHomeomorph.refl_apply, id_eq, heq]
  split_ifs with h
  · exact coordinateTriangleAngle_eq_tangentMetric g F hF hFi q hq _ hb i h
  · rfl

end PoincareMT.Topology.Surface
