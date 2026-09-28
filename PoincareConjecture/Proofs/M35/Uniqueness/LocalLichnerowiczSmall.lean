import PoincareConjecture.Proofs.M35.Uniqueness.LocalSmallSubsolution
import PoincareConjecture.Proofs.M35.Uniqueness.LichnerowiczEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_lichnerowicz_small
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B δ : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (hδ : 0 < δ) {C₀ : Set StandardCapSpace} (hC₀ : IsCompact C₀) :
    ∃ S : Set StandardCapSpace, IsCompact S ∧ C₀ ⊆ S ∧
      ∀ H : ℝ → CovariantTensorEvaluation 3 StandardCapSpace 2,
        (∀ s, IsSmoothCovariantTensor (H s)) →
        ContinuousOn (fun z : ℝ × StandardCapSpace =>
          ((G.flow.metric z.1).tensorNorm (H z.1) z.2) ^ 2) (Icc 0 T ×ˢ S) →
        (∀ x ∈ S, ∀ v, H 0 x v = 0) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ S, ((G.flow.metric t).tensorNorm (H t) x) ^ 2 ≤ B) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ S, ∀ v, HasDerivAt (fun s => H s x v)
          ((G.flow.connection t).tensorLaplacian (H t) x v +
            lichnerowiczReaction (G.flow.connection t) (H t) x v) t) →
        ∀ t ∈ Icc 0 T, ∀ x ∈ C₀, ((G.flow.metric t).tensorNorm (H t) x) ^ 2 ≤ δ := by
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  obtain ⟨S, hS, hCS, hcomparison⟩ := exists_raw_local_small_subsolution P G hT hTlt hB
    (show 0 ≤ 324 * K from mul_nonneg (by norm_num) hK) hδ hC₀
  refine ⟨S, hS, hCS, ?_⟩
  intro H hH hcont hinit hbound hheat
  let Q : ℝ → StandardCapSpace → ℝ := fun t x =>
    ((G.flow.metric t).tensorNorm (H t) x) ^ 2
  refine hcomparison Q hcont (fun t _ x _ => ?_) (fun x hx => ?_) hbound ?_
  · exact (M04.contMDiff_tensorNorm_sq (G.flow.metric t) (hH t)).contMDiffAt
  · simp [Q, RiemannianMetric.tensorNorm, hinit x hx]
  · intro t ht x hx
    have hti : t ∈ interior (Ico 0 G.lifetime) := by
      rw [interior_Ico]
      exact ⟨ht.1, ht.2.trans_lt hTlt⟩
    obtain ⟨a, ha, hle⟩ := lichnerowicz_normSq_heat_le G.flow H hH hti x hK
      ((le_abs_self _).trans (hRm t ⟨ht.1.le, ht.2⟩ x)) (hheat t ht x hx)
    refine ⟨a, ha.hasDerivWithinAt, ?_⟩
    change a ≤ (G.flow.connection t).laplacian (Q t) x +
      (4 * (3 : ℝ) ^ 4 * K) * Q t x at hle
    norm_num at hle
    exact hle

end PoincareConjecture.M35.Uniqueness
