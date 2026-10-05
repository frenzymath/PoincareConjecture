import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.MetricConvergence
import PoincareLib.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Guarded inverses of the actual regular convergence stages

Each retained source embedding is a partial diffeomorphism with its exact
exhaustion stage as source and the actual embedding image as target. The
inverse is used only on that image. This supplies initial-neck persistence
in Morgan--Tian Proposition 10.7, p. 253; M28 derivation 88.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u}
  [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}

/-- The original embedding and its guarded smooth inverse form a partial
diffeomorphism of the actual regular stage. Source: Proposition 10.7,
p. 253; M28 derivation 88. No radial convergence field is used. -/
noncomputable def stageDiffeomorph (G : RegularPointedMetricConvergence g p) (j : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    PartialDiffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier (M (G.subsequence j)) ∞ := by
  classical
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let U := G.exhaustion j
  let f := G.embedding j
  letI : Nonempty U := ⟨⟨G.base, G.base_in_exhaustion j⟩⟩
  let ginv : M (G.subsequence j) → G.limitCarrier.carrier :=
    fun y => (Function.invFun (fun x : U => f x) y : U).val
  have hleft : ∀ x ∈ U, ginv (f x) = x := by
    intro x hx
    exact congrArg Subtype.val
      (Function.leftInverse_invFun (G.embedding_open j).injective ⟨x, hx⟩)
  have hginv_smooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ginv (f '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply Poincare.contMDiffAt_of_local_left_inverse
      (G.embedding_smooth j ⟨x, hx⟩).contMDiffAt
      ((G.embedding_smooth j ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
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
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := ?_
    left_inv' := hleft
    right_inv' := ?_
    open_source := G.exhaustion_open j
    open_target := htarget_open
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := hginv_smooth }
  · rintro _ ⟨x, hx, rfl⟩
    rw [hleft x hx]
    exact hx
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg f (hleft x hx)
  · intro x hx
    exact (G.embedding_smooth j ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/-- The partial diffeomorphism uses exactly the retained exhaustion stage.
Source: Theorem 5.6 and Proposition 10.7; M28 derivation 88. -/
@[simp] theorem stageDiffeomorph_source
    (G : RegularPointedMetricConvergence g p) (j : ℕ) :
    (G.stageDiffeomorph j).source = G.exhaustion j := rfl

/-- The inverse domain is exactly the original source embedding image.
Source: Proposition 10.7, p. 253; M28 derivation 88. -/
@[simp] theorem stageDiffeomorph_target
    (G : RegularPointedMetricConvergence g p) (j : ℕ) :
    (G.stageDiffeomorph j).target = G.embedding j '' G.exhaustion j := rfl

/-- The forward map remains the original total embedding, so all guarded
metric identities use the same source map. Source: M28 derivation 88. -/
@[simp] theorem stageDiffeomorph_apply
    (G : RegularPointedMetricConvergence g p) (j : ℕ) (x : G.limitCarrier.carrier) :
    G.stageDiffeomorph j x = G.embedding j x := rfl

end PoincareMT.M28.RegularPointedMetricConvergence
