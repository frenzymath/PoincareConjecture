import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SurvivalSlice
import PoincareConjecture.Proofs.M09.ManifoldLocalInverse

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

theorem survivalSlice_local_inverse
    (E : M14ExponentialFamily G T x) (htau : 0 ≤ tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hbij : Function.Bijective (E.differential Z (Real.sqrt tau) hZ)) :
    ∃ e : OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - tau)).Point,
      Z ∈ e.source ∧
      (∀ W ∈ e.source, (W, Real.sqrt tau) ∈ E.domain) ∧
      EqOn e (survivalSliceMap E tau htau q0) e.source := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let : T2Space (G.Horizontal x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let D := {W : G.Horizontal x | (W, Real.sqrt tau) ∈ E.domain}
  have hsm : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞
      (survivalSliceMap E tau htau q0) D := fun W hW =>
    (survivalSliceMap_smooth E htau q0 hW).contMDiffWithinAt
  obtain ⟨e, hZe, heD, hef, _, _⟩ := M09.exists_manifold_local_inverse
    (survivalSliceMap E tau htau q0) D (survival_domain_open E _) hsm Z hZ
    ((survivalSliceMap_differential_bijective_iff E htau q0 hZ).mpr hbij)
  exact ⟨e, hZe, fun _ hW => heD hW, hef⟩

end PoincareConjecture.Proofs.M46
