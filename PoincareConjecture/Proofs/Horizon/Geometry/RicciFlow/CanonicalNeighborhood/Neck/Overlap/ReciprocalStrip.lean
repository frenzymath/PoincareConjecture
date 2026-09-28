import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.FrontierHeight
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem subset_region_of_avoids_boundary_slices (N : EpsilonNeck g)
    {a b : ℝ} (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    {T : Set M} (hT : IsPreconnected T)
    (hmeet : (T ∩ N.region a b).Nonempty)
    (hfaces : ∀ q : UnitTwoSphere,
      N.coordinate_map (q, a) ∉ T ∧ N.coordinate_map (q, b) ∉ T) :
    T ⊆ N.region a b := by
  let K := N.coordinate_map '' (univ ×ˢ Icc a b)
  have hK : IsCompact K := N.isCompact_coordinate_slab ha hb
  have hreg : N.region a b ⊆ K := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  apply hT.subset_of_closure_inter_subset (N.isOpen_region a b) hmeet
  rintro x ⟨hx, hxT⟩
  obtain ⟨z, hz, rfl⟩ := closure_minimal hreg hK.isClosed hx
  have hzdom : z ∈ N.cylinderDomain :=
    ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hza : a < z.2 := lt_of_le_of_ne hz.2.1 (by
    intro heq
    have hzEq : z = (z.1, a) := Prod.ext rfl heq.symm
    exact (hfaces z.1).1 (hzEq ▸ hxT))
  have hzb : z.2 < b := lt_of_le_of_ne hz.2.2 (by
    intro heq
    have hzEq : z = (z.1, b) := Prod.ext rfl heq
    exact (hfaces z.1).2 (hzEq ▸ hxT))
  refine ⟨N.coordinate_map_mem hzdom, ?_⟩
  simpa only [N.coordinate_inverse_coordinate_map hzdom] using And.intro hza hzb

theorem signed_strip_subset_of_frontier_height_bounds (N P : EpsilonNeck g)
    (heq : P.epsilon = N.epsilon) (hsmall : N.epsilon ≤ 1 / 10000)
    (hquarter : closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆ P.carrier)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hheight : ∀ (q : UnitTwoSphere) (a : ℝ), a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ →
      -(1.1 : ℝ) * (N.epsilon⁻¹ - a) - 5 * Real.pi ≤
          σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ∧
        σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ≤
          -(0.9 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi) :
    {y : M | y ∈ P.carrier ∧ -(0.08 : ℝ) * N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
      σ * (P.coordinate_inverse y).2 < -(0.02 : ℝ) * N.epsilon⁻¹} ⊆
        N.region ((0.9 : ℝ) * N.epsilon⁻¹) ((0.99 : ℝ) * N.epsilon⁻¹) := by
  let r := N.epsilon⁻¹
  have hr : 0 < r := inv_pos.mpr N.epsilon_pos
  have hrlarge : (10000 : ℝ) ≤ r := by
    change 10000 ≤ N.epsilon⁻¹
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  let T : Set M := {y | y ∈ P.carrier ∧ -(0.08 : ℝ) * r < σ * (P.coordinate_inverse y).2 ∧
    σ * (P.coordinate_inverse y).2 < -(0.02 : ℝ) * r}
  have hT : IsPreconnected T := by
    rcases hσ with rfl | rfl
    · have hTeq : T = P.region (-(0.08 : ℝ) * r) (-(0.02 : ℝ) * r) := by
        ext y
        simp only [T, region, mem_ofPred_eq, one_mul]
      rw [hTeq]
      apply (P.isConnected_region ?_ ?_ ?_).2
      · rw [heq]; change -r ≤ -(0.08 : ℝ) * r; linarith
      · rw [heq]; change -(0.02 : ℝ) * r ≤ r; linarith
      · linarith
    · have hTeq : T = P.region ((0.02 : ℝ) * r) ((0.08 : ℝ) * r) := by
        ext y
        simp only [T, region, mem_ofPred_eq, neg_one_mul]
        constructor <;> rintro ⟨hy, h₁, h₂⟩ <;> refine ⟨hy, ?_, ?_⟩ <;> linarith
      rw [hTeq]
      apply (P.isConnected_region ?_ ?_ ?_).2
      · rw [heq]; change -r ≤ (0.02 : ℝ) * r; linarith
      · rw [heq]; change (0.08 : ℝ) * r ≤ r; linarith
      · linarith
  apply N.subset_region_of_avoids_boundary_slices
    (by change -r < (0.9 : ℝ) * r; linarith)
    (by change (0.99 : ℝ) * r < r; linarith) hT
  · let q := (N.coordinate_inverse N.center).1
    let a := (0.95 : ℝ) * r
    have ha : a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
      change r / 2 < (0.95 : ℝ) * r ∧ (0.95 : ℝ) * r < r
      constructor <;> linarith
    have hqa : (q, a) ∈ N.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      change -r < (0.95 : ℝ) * r ∧ (0.95 : ℝ) * r < r
      constructor <;> linarith
    have hqaQuarter : N.coordinate_map (q, a) ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
      refine ⟨N.coordinate_map_mem hqa, ?_⟩
      simpa only [N.coordinate_inverse_coordinate_map hqa, mem_Ioo] using ha
    have hh := hheight q a ha
    change -(1.1 : ℝ) * (r - (0.95 : ℝ) * r) - 5 * Real.pi ≤ _ ∧
      _ ≤ -(0.9 : ℝ) * (r - (0.95 : ℝ) * r) + 5 * Real.pi at hh
    refine ⟨N.coordinate_map (q, a), ?_, N.coordinate_map_mem hqa, ?_⟩
    · exact ⟨hquarter (subset_closure hqaQuarter), by nlinarith [Real.pi_le_four],
        by nlinarith [Real.pi_le_four]⟩
    · rw [N.coordinate_inverse_coordinate_map hqa]
      change (0.9 : ℝ) * r < (0.95 : ℝ) * r ∧ (0.95 : ℝ) * r < (0.99 : ℝ) * r
      constructor <;> linarith
  · intro q
    constructor
    · intro hy
      have hh := (hheight q ((0.9 : ℝ) * r) (by
        change r / 2 < (0.9 : ℝ) * r ∧ (0.9 : ℝ) * r < r
        constructor <;> linarith)).2
      change _ ≤ -(0.9 : ℝ) * (r - (0.9 : ℝ) * r) + 5 * Real.pi at hh
      have hylo := hy.2.1
      nlinarith [Real.pi_le_four]
    · intro hy
      have hh := (hheight q ((0.99 : ℝ) * r) (by
        change r / 2 < (0.99 : ℝ) * r ∧ (0.99 : ℝ) * r < r
        constructor <;> linarith)).1
      change -(1.1 : ℝ) * (r - (0.99 : ℝ) * r) - 5 * Real.pi ≤ _ at hh
      have hyhi := hy.2.2
      nlinarith [Real.pi_le_four]

theorem exists_reciprocal_strip_of_positive_frontier_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          {y : M | y ∈ P.carrier ∧ -(0.08 : ℝ) * N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
            σ * (P.coordinate_inverse y).2 < -(0.02 : ℝ) * N.epsilon⁻¹} ⊆
              N.region ((0.9 : ℝ) * N.epsilon⁻¹) ((0.99 : ℝ) * N.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, _, hheight⟩ := exists_frontier_transition_height_bounds.{u}
  obtain ⟨ε₂, hε₂, _, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  refine ⟨min ε₁ (min ε₂ (1 / 10000)), lt_min hε₁ (lt_min hε₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  obtain ⟨σ, hσ, hh⟩ := hheight N P (hε.trans (min_le_left _ _)) heq x hxfront hx hxP
  have hquarter := hcontain N P
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) heq ⟨x, hx, hxP⟩
  exact ⟨σ, hσ, signed_strip_subset_of_frontier_height_bounds N P heq
    (hε.trans ((min_le_right _ _).trans (min_le_right _ _))) hquarter hσ hh⟩

theorem exists_shifted_slice_subset_positive_end_of_frontier_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          range (fun q : UnitTwoSphere => P.coordinate_map (q, σ * (0.05 : ℝ) * N.epsilon⁻¹)) ⊆
            N.region ((0.9 : ℝ) * N.epsilon⁻¹) N.epsilon⁻¹ := by
  obtain ⟨ε₀, hε₀, hsmall, hstrip⟩ := exists_reciprocal_strip_of_positive_frontier_contact.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  obtain ⟨σ, hσ, hsub⟩ := hstrip N P hε heq x hxfront hx hxP
  have hr : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  refine ⟨-σ, ?_, ?_⟩
  · rcases hσ with rfl | rfl <;> norm_num
  · rintro y ⟨q, rfl⟩
    have hdom : (q, -σ * (0.05 : ℝ) * N.epsilon⁻¹) ∈ P.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      rw [heq]
      rcases hσ with rfl | rfl <;> constructor <;> nlinarith
    have hheight : σ * (-σ * (0.05 : ℝ) * N.epsilon⁻¹) = -(0.05 : ℝ) * N.epsilon⁻¹ := by
      rcases hσ with rfl | rfl <;> ring
    have hy := hsub (show P.coordinate_map (q, -σ * (0.05 : ℝ) * N.epsilon⁻¹) ∈
        {y : M | y ∈ P.carrier ∧ -(0.08 : ℝ) * N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
          σ * (P.coordinate_inverse y).2 < -(0.02 : ℝ) * N.epsilon⁻¹} from by
      refine ⟨P.coordinate_map_mem hdom, ?_⟩
      rw [P.coordinate_inverse_coordinate_map hdom, hheight]
      constructor <;> linarith)
    exact ⟨hy.1, hy.2.1, hy.2.2.trans (by linarith)⟩

end PoincareConjecture.EpsilonNeck
