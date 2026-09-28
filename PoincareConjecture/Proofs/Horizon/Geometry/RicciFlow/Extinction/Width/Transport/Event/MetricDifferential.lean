import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Differential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle NNReal ENNReal

namespace PoincareConjecture

theorem m67_inner_mfderiv_le_of_distance_bound
    {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [T2Space N]
    (g : RiemannianMetric m M) (h : RiemannianMetric n N)
    {f : M → N} (hf : MDifferentiable (𝓡 m) (𝓡 n) f)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * g.edist x y)
    (x : M) (v : TangentSpace (𝓡 m) x) :
    h.inner (f x) (mfderiv (𝓡 m) (𝓡 n) f x v) (mfderiv (𝓡 m) (𝓡 n) f x v) ≤
      L ^ 2 * g.inner x v v := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) N
  let : RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 m) M
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let : IsRiemannianManifold (𝓡 m) M := ⟨fun _ _ => rfl⟩
  let : IsRiemannianManifold (𝓡 n) N := ⟨fun _ _ => rfl⟩
  have hLip : LipschitzWith (NNReal.mk L hL) f := by
    intro x y
    change h.edist (f x) (f y) ≤ (NNReal.mk L hL : ℝ≥0∞) * g.edist x y
    simpa only [ENNReal.ofReal_eq_coe_nnreal hL] using hbound x y
  have hb := m67_norm_mfderiv_apply_le_of_lipschitz hf hLip x v
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hsq
  exact hsq

end PoincareConjecture
