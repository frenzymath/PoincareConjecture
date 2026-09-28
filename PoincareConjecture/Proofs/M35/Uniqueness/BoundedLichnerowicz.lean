import PoincareConjecture.Proofs.M35.Uniqueness.LichnerowiczEnergy
import PoincareConjecture.Proofs.M35.Uniqueness.CompleteScalarMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem bounded_lichnerowicz_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (H : ℝ → CovariantTensorEvaluation 3 StandardCapSpace 2)
    (hH : ∀ s, IsSmoothCovariantTensor (H s))
    (hcont : ContinuousOn (fun z : ℝ × StandardCapSpace =>
      ((G.flow.metric z.1).tensorNorm (H z.1) z.2) ^ 2) (Icc 0 T ×ˢ univ))
    (hinit : ∀ x v, H 0 x v = 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, ((G.flow.metric t).tensorNorm (H t) x) ^ 2 ≤ B)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x v, HasDerivAt (fun s => H s x v)
      ((G.flow.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (G.flow.connection t) (H t) x v) t) :
    ∀ t ∈ Icc 0 T, ∀ x v, H t x v = 0 := by
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  let Q : ℝ → StandardCapSpace → ℝ := fun t x =>
    ((G.flow.metric t).tensorNorm (H t) x) ^ 2
  have hQs (t : ℝ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t) :=
    M04.contMDiff_tensorNorm_sq (G.flow.metric t) (hH t)
  have hnonneg := raw_scalar_nonnegative P G hT hTlt hB
    (show 0 ≤ 324 * K from mul_nonneg (by norm_num) hK)
    (fun t x => -Q t x) hcont.neg
    (fun t _ x => (hQs t x).neg)
    (fun x => by simp [Q, RiemannianMetric.tensorNorm, hinit])
    (fun t ht x => by dsimp [Q]; linarith [hbound t ht x])
    (fun t ht x => ?_)
  · intro t ht x v
    have hQ : Q t x = 0 := le_antisymm (by linarith [hnonneg t ht x]) (sq_nonneg _)
    have hv := M04.tensorEvaluation_sq_le_tensorNorm (G.flow.metric t) (hH t) x v
    change (H t x v) ^ 2 ≤ Q t x * _ at hv
    rw [hQ, zero_mul] at hv
    exact sq_eq_zero_iff.mp (le_antisymm hv (sq_nonneg _))
  · have hti : t ∈ interior (Ico 0 G.lifetime) := by
      rw [interior_Ico]
      exact ⟨ht.1, ht.2.trans_lt hTlt⟩
    obtain ⟨a, ha, hle⟩ := lichnerowicz_normSq_heat_le G.flow H hH hti x hK
      ((le_abs_self _).trans (hRm t ⟨ht.1.le, ht.2⟩ x)) (hheat t ht x)
    refine ⟨-a, ha.neg.hasDerivWithinAt, ?_⟩
    have hneg : (fun y => -Q t y) = fun y => (-1 : ℝ) * Q t y := by
      funext y
      ring
    rw [hneg, LeviCivitaData.laplacian_const_mul]
    change a ≤ (G.flow.connection t).laplacian (Q t) x +
      (4 * (3 : ℝ) ^ 4 * K) * Q t x at hle
    norm_num at hle
    linarith

end PoincareConjecture.M35.Uniqueness
