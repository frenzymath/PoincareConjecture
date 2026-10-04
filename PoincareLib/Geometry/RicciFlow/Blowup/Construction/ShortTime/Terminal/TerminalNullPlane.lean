import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.NullPlane

/-!
# Terminal null planes on finite closed slabs

At the terminal time of a nonnegatively curved flow, a zero sectional
component has nonpositive backward-endpoint evolution. Its nonnegative
diffusion term then forces nonpositive reaction. These are the local
endpoint inputs to Morgan--Tian Claim 11.7, pp. 270-271, and Corollary 4.19,
pp. 71-72. The argument adapts the legal Horizon ancient null-plane lemmas
to the literal finite interval; see finite-terminal-null-plane.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M30

/-- A null plane at the terminal endpoint of a nontrivial finite slab has
nonpositive curvature evolution (Claim 11.7, pp. 270-271). This is the
finite version of RicciFlow.curvatureEvolution_nonpos_on_terminal_null_plane. -/
theorem curvatureEvolution_nonpos_on_finite_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).tensorLaplacian (F.connection b).riemannEvaluation x ![v, w, v, w] +
      (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hmin : IsMinOn (fun t => (F.connection t).curvatureTensor x v w v w)
      (Icc a b) b := by
    intro t ht
    change (F.connection b).curvatureTensor x v w v w ≤ _
    rw [hzero]
    exact (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht x) v w
  have hcone : a - b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset hb ⟨le_rfl, hab.le⟩)
  have h := hmin.localize.hasFDerivWithinAt_nonneg
    (hC.curvature_evolution n M (Icc a b) F b hb x v w v w).hasFDerivWithinAt hcone
  change 0 ≤ (a - b) * (_ + _) at h
  nlinarith

/-- Nonnegative diffusion forces nonpositive reaction at a finite terminal
null plane (Claim 11.7, pp. 270-271; Corollary 4.19, pp. 71-72). This uses
the existing static null-plane Laplacian theorem on the same connection. -/
theorem curvatureReaction_nonpos_on_finite_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hlap := (F.connection b).tensorLaplacian_nonneg_on_null_plane
    (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (fun y u z => (F.connection b).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator b hb y) u z) x v w hzero
  have hevol := curvatureEvolution_nonpos_on_finite_terminal_null_plane
    hab hC F hoperator x v w hzero
  linarith

end PoincareMT.M30
