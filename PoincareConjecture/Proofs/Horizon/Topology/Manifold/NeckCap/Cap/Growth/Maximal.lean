import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.Termination
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cover
import Mathlib.Order.WellFounded

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_maximal_cap_growth_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {B ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ A : Set (CapCertificate g),
        (∀ C ∈ A, C.cap_constant ≤ B) → (∀ C ∈ A, C.epsilon = ε) →
        ∀ C₀ ∈ A, ∃ C ∈ A, C₀.carrier ⊆ C.carrier ∧
          ∀ D ∈ A, C.carrier ⊆ D.carrier → Disjoint (frontier C.carrier) D.closed_core := by
  obtain ⟨ε₀, hε₀, hsmall, htermination⟩ := exists_cap_growth_termination_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g B ε hεpos hε A hB hsame C₀ hC₀
  let R : A → A → Prop := fun D C =>
    C.val.carrier ⊆ D.val.carrier ∧ (frontier C.val.carrier ∩ D.val.closed_core).Nonempty
  have hwf : WellFounded R := by
    apply wellFounded_iff_isEmpty_descending_chain.mpr
    refine ⟨?_⟩
    rintro ⟨S, hS⟩
    exact htermination hεpos hε (fun n => (S n).val)
      (fun n => hB _ (S n).property) (fun n => hsame _ (S n).property) hS
  let T : Set A := {C | C₀.carrier ⊆ C.val.carrier}
  obtain ⟨C, hC, hmax⟩ := hwf.has_min T ⟨⟨C₀, hC₀⟩, Subset.rfl⟩
  refine ⟨C.val, C.property, hC, ?_⟩
  intro D hD hCD
  apply disjoint_iff_inter_eq_empty.mpr
  apply not_nonempty_iff_eq_empty.mp
  intro hcontact
  exact hmax ⟨D, hD⟩ (hC.trans hCD) ⟨hCD, hcontact⟩

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.ConnectedNeckCapCover

theorem exists_maximal_cap_growth_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
        ∀ C₀ ∈ H.caps, ∃ C ∈ H.caps, C₀.carrier ⊆ C.carrier ∧
          ∀ D ∈ H.caps, C.carrier ⊆ D.carrier →
            Disjoint (frontier C.carrier) D.closed_core := by
  obtain ⟨ε₀, hε₀, hsmall, hmax⟩ := CapCertificate.exists_maximal_cap_growth_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C₀ hC₀
  exact hmax H.epsilon_pos hε H.caps H.cap_constant_bound H.cap_epsilon C₀ hC₀

end PoincareConjecture.ConnectedNeckCapCover
