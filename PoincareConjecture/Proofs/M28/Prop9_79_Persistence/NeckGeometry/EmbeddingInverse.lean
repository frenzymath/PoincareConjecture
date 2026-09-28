import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.NeckGeometry

noncomputable def stageInverse
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) (j : ℕ) :
    M (G.subsequence j) → G.limitCarrier.carrier := by
  classical
  let U := G.exhaustion j
  let f := G.embedding j
  have hU : U.Nonempty := ⟨G.base, G.base_in_exhaustion j⟩
  letI : Nonempty U := hU.to_subtype
  exact fun y => (Function.invFun (fun x : U => f x) y : U)

noncomputable def stageDiffeomorph
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) (j : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    PartialDiffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier
      (M (G.subsequence j)) ∞ := by
  classical
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let U := G.exhaustion j
  let f := G.embedding j
  let ginv : M (G.subsequence j) → G.limitCarrier.carrier := stageInverse G j
  have hU : U.Nonempty := ⟨G.base, G.base_in_exhaustion j⟩
  have hleft : ∀ x ∈ U, ginv (f x) = x := by
    intro x hx
    let : Nonempty U := hU.to_subtype
    dsimp [ginv, stageInverse]
    exact congrArg Subtype.val
      (Function.leftInverse_invFun (G.embedding_open j).injective ⟨x, hx⟩)
  have hginv_smooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ginv (f '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply Poincare.contMDiffAt_of_local_left_inverse
      ((G.embedding_smooth j ⟨x, hx⟩).contMDiffAt)
      ((G.embedding_smooth j ⟨x, hx⟩).mfderivToContinuousLinearEquiv
        (by simp)).bijective
    filter_upwards [(G.exhaustion_open j).mem_nhds hx] with z hz
    exact hleft z hz
  have htarget_open : IsOpen (f '' U) := by
    have h := (G.embedding_open j).isOpenMap (Set.univ : Set U) isOpen_univ
    have heq : (fun x : U => f x) '' (Set.univ : Set U) = f '' U := by
      ext y
      constructor
      · rintro ⟨x, _, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    rw [← heq]
    exact h
  refine {
    toFun := f
    invFun := ginv
    source := U
    target := f '' U
    map_source' := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    map_target' := by
      rintro y ⟨x, hx, rfl⟩
      have heq : ginv (f x) = x := hleft x hx
      rw [heq]
      exact hx
    left_inv' := by
      intro x hx
      exact hleft x hx
    right_inv' := by
      rintro y ⟨x, hx, rfl⟩
      exact congrArg f (hleft x hx)
    open_source := G.exhaustion_open j
    open_target := htarget_open
    contMDiffOn_toFun := by
      intro x hx
      exact (G.embedding_smooth j ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt
    contMDiffOn_invFun := hginv_smooth }

@[simp] theorem stageDiffeomorph_source
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) (j : ℕ) :
    (stageDiffeomorph G j).source = G.exhaustion j := rfl

@[simp] theorem stageDiffeomorph_target
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) (j : ℕ) :
    (stageDiffeomorph G j).target = G.embedding j '' G.exhaustion j := rfl

end PoincareConjecture.M28.NeckGeometry
