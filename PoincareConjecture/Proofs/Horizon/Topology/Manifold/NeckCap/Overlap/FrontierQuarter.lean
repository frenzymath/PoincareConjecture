import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ReciprocalQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.SliceAgreement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_frontier_reversal_quarter_overlap :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        P.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        P.center ∉ N.carrier →
          ∃ Q : EpsilonNeck g, (Q = P ∨ Q = P.reversed) ∧
            N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ Q.carrier ∧
            Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
              N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) ∧
            (Q.IsSeparating ↔ N.IsSeparating) ∧
            (Q.IsNonseparating ↔ N.IsNonseparating) := by
  obtain ⟨ε₁, hε₁, hsmall, hrecip⟩ := exists_reciprocal_quarter_of_positive_frontier_contact.{u}
  obtain ⟨ε₂, hε₂, _, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  obtain ⟨ε₃, hε₃, _, hagree⟩ := exists_contained_slice_separation_agreement.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    ((min_le_left _ _).trans hsmall).trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq hx hout
  have hfront : P.center ∈ frontier N.carrier := by
    rw [N.carrier_open.frontier_eq]
    exact ⟨closure_mono (N.region_subset_carrier _ _) hx, hout⟩
  obtain ⟨σ, hσ, hnegative⟩ := hrecip N P (hε.trans (min_le_left _ _)) heq
    P.center hfront hx P.center_on_central_sphere
  have hpositive := hcontain N P (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))
    heq ⟨P.center, hx, P.center_on_central_sphere⟩
  have horiented : ∃ Q : EpsilonNeck g, (Q = P ∨ Q = P.reversed) ∧
      Q.carrier = P.carrier ∧ Q.epsilon = N.epsilon ∧
      Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
        N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) := by
    rcases hσ with rfl | rfl
    · refine ⟨P, Or.inl rfl, rfl, heq, ?_⟩
      intro y hy
      apply hnegative
      simpa only [region, mem_ofPred_eq, one_mul] using hy
    · refine ⟨P.reversed, Or.inr rfl, rfl, heq, ?_⟩
      intro y hy
      apply hnegative
      simpa only [region, mem_ofPred_eq, reversed_carrier,
        reversed_coordinate_inverse, neg_one_mul] using hy
  obtain ⟨Q, hQ, hcarrier, hQε, hnegativeQ⟩ := horiented
  have hR : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have ha : -(0.75 : ℝ) * N.epsilon⁻¹ ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ := by
    rw [hQε]
    constructor <;> linarith
  have hslice (q : UnitTwoSphere) :
      Q.coordinate_map (q, -(0.75 : ℝ) * N.epsilon⁻¹) ∈ N.carrier := by
    apply (hnegativeQ ?_).1
    refine ⟨Q.coordinate_map_mem ⟨mem_univ _, ha⟩, ?_⟩
    rw [Q.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩]
    constructor <;> linarith
  have hNε := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsep := hagree N Q hNε (hQε.trans_le hNε) ha hslice
  refine ⟨Q, hQ, ?_, hnegativeQ, hsep⟩
  rw [hcarrier]
  exact subset_closure.trans hpositive

end PoincareConjecture.EpsilonNeck
