import PoincareLib.Topology.VectorBundle.CompactFrame
import PoincareLib.Geometry.RicciFlow.Harnack.Finite

/-!
# Compact Hamilton test directions

Orthonormal tangent frames and normalized skew/vector coefficients give a
compact parameter space above a compact spatial set. The metric is fixed,
so these parameters can be used throughout a compact time interval.

Source: Chow et al., Part II, Section 15.4.5, p. 287.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

namespace Poincare.RicciFlow.Harnack

open PoincareMT Poincare.VectorBundle

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Compactness of all normalized Hamilton directions expressed in arbitrary
orthonormal frames of one fixed reference metric. -/
theorem isCompact_normalized_hamilton_directions [T2Space M]
    (g : RiemannianMetric n M) {K : Set M} (hK : IsCompact K) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsCompact {q : fiberFamilies (F := EuclideanSpace ℝ (Fin n))
        (E := TangentSpace (𝓡 n)) (Fin n) ×
        EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n) |
      q.1.val.1 ∈ K ∧ Orthonormal ℝ (FiberFamily.vector q.1) ∧ ‖q.2‖ = 1 ∧
        ∀ i j, q.2 (Sum.inl (i, j)) = -q.2 (Sum.inl (j, i))} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let A := fiberFamilies (F := EuclideanSpace ℝ (Fin n))
    (E := (TangentSpace (𝓡 n) : M → Type _)) (Fin n)
  let C := EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n)
  have hframe := isCompact_orthonormalFamilies_over
    (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (I := Fin n) hK
  have hskew : IsClosed {q : A × C |
      ∀ i j, q.2 (Sum.inl (i, j)) = -q.2 (Sum.inl (j, i))} := by
    have heq : {q : A × C | ∀ i j, q.2 (Sum.inl (i, j)) = -q.2 (Sum.inl (j, i))} =
        ⋂ i, ⋂ j, {q : A × C | q.2 (Sum.inl (i, j)) = -q.2 (Sum.inl (j, i))} := by
      ext q
      simp only [mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ((PiLp.continuous_apply 2 _ (Sum.inl (i, j))).comp continuous_snd)
        (((PiLp.continuous_apply 2 _ (Sum.inl (j, i))).comp continuous_snd).neg)
  have h := (hframe.prod (isCompact_sphere (0 : C) 1)).inter_right hskew
  convert h using 1
  ext q
  simp only [mem_inter_iff, mem_prod, mem_ofPred_eq, Metric.mem_sphere,
    dist_zero_right]
  tauto

end Poincare.RicciFlow.Harnack
