import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ClosingSlice











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem truncated_sides_components (D : CapCertificate g)
    {U K : Set M} (hU : IsOpen U) (hcU : IsConnected U) (hK : IsClosed K)
    {s η : ℝ} (hη : 0 < η) (hlo : -D.epsilon⁻¹ < s - η)
    (hhi : s + η < D.epsilon⁻¹)
    (hcollar : D.end_neck.region (s - η) (s + η) ⊆ U)
    (hint : interior K = D.closed_core ∪ D.end_neck.region (-D.epsilon⁻¹) s)
    (hfront : frontier K = range (fun q : UnitTwoSphere =>
      D.end_neck.coordinate_map (q, s))) :
    IsConnected (U ∩ interior K) ∧ IsConnected (U \ K) ∧
      (U ∩ interior K) ∪ (U \ K) = U \ frontier K ∧
      (∀ x ∈ U ∩ interior K,
        connectedComponentIn (U \ frontier K) x = U ∩ interior K) ∧
      ∀ x ∈ U \ K, connectedComponentIn (U \ frontier K) x = U \ K := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let V := D.end_neck.region (s - η) (s + η)
  have hs : s ∈ Ioo (-D.end_neck.epsilon⁻¹) D.end_neck.epsilon⁻¹ := by
    rw [D.end_neck_epsilon]
    constructor <;> linarith
  have hfrontV : frontier K ⊆ V := by
    rw [hfront]
    rintro x ⟨q, rfl⟩
    have hdom : (q, s) ∈ D.end_neck.cylinderDomain := ⟨mem_univ _, hs⟩
    refine ⟨D.end_neck.coordinate_map_mem hdom, ?_⟩
    rw [D.end_neck.coordinate_inverse_coordinate_map hdom]
    constructor <;> dsimp <;> linarith
  have hleft : interior K ∩ V = D.end_neck.region (s - η) s := by
    rw [hint]
    apply Subset.antisymm
    · rintro x ⟨hc | he, hxV⟩
      · exact (disjoint_left.mp D.disjoint_closed_core_end hc hxV.1).elim
      · exact ⟨he.1, hxV.2.1, he.2.2⟩
    · intro x hx
      refine ⟨Or.inr ⟨hx.1, hlo.trans hx.2.1, hx.2.2⟩, hx.1, hx.2.1, ?_⟩
      linarith [hx.2.2]
  have hmemK (x : M) (hx : x ∈ V) :
      x ∈ K ↔ (D.end_neck.coordinate_inverse x).2 ≤ s := by
    constructor
    · intro hxK
      by_cases hi : x ∈ interior K
      · rw [hint] at hi
        rcases hi with hc | he
        · exact (disjoint_left.mp D.disjoint_closed_core_end hc hx.1).elim
        · exact he.2.2.le
      · have hf : x ∈ frontier K := hK.frontier_eq ▸ ⟨hxK, hi⟩
        rw [hfront] at hf
        obtain ⟨q, rfl⟩ := hf
        rw [D.end_neck.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · apply interior_subset
        rw [hint]
        exact Or.inr ⟨hx.1, hlo.trans hx.2.1, hlt⟩
      · apply hK.closure_eq ▸ frontier_subset_closure (s := K)
        rw [hfront]
        refine ⟨(D.end_neck.coordinate_inverse x).1, ?_⟩
        rw [← heq]
        exact D.end_neck.coordinate_map_coordinate_inverse hx.1
  have hright : Kᶜ ∩ V = D.end_neck.region s (s + η) := by
    apply Subset.antisymm
    · rintro x ⟨hxK, hxV⟩
      exact ⟨hxV.1, lt_of_not_ge (fun h => hxK ((hmemK x hxV).mpr h)), hxV.2.2⟩
    · intro x hx
      have hxV : x ∈ V := ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
      exact ⟨fun hxK => (not_lt_of_ge ((hmemK x hxV).mp hxK)) hx.2.1, hxV⟩
  apply Poincare.Topology.connected_components_of_closed_cut hU hcU hK
    (D.end_neck.isOpen_region _ _) hcollar hfrontV
  · rw [hleft]
    apply D.end_neck.isConnected_region
    · rw [D.end_neck_epsilon]; exact hlo.le
    · rw [D.end_neck_epsilon]; linarith
    · linarith
  · rw [hright]
    apply D.end_neck.isConnected_region
    · rw [D.end_neck_epsilon]; linarith
    · rw [D.end_neck_epsilon]; exact hhi.le
    · linarith



theorem exists_second_cap_essential_components_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ ε₀ →
          ∀ {U : Set M}, IsOpen U → IsConnected U → C.end_neck.carrier ⊆ U →
            Disjoint C.closed_core U → Disjoint D.closed_core C.carrier →
            Disjoint C.closed_core D.carrier →
            IsCompact (C.carrier ∪ U ∪ D.carrier) →
            (frontier (C.carrier ∪ U) ∩ D.core).Nonempty →
            ∃ s ∈ Ioo 0 D.epsilon⁻¹, ∃ η : ℝ, 0 < η ∧ 0 < s - η ∧
              s + η < D.epsilon⁻¹ ∧ D.end_neck.region (s - η) (s + η) ⊆ U ∧
              D.end_neck.region (s - η) D.epsilon⁻¹ ⊆ U ∧
              let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
              IsCompact K ∧ K ⊆ D.carrier ∧ D.closed_core ⊆ interior K ∧
                frontier K = range (fun q : UnitTwoSphere =>
                  D.end_neck.coordinate_map (q, s)) ∧
                D.carrier ∩ U = (U ∩ interior K) ∪
                  D.end_neck.region (s - η) D.epsilon⁻¹ ∧
                (U ∩ interior K) ∩ D.end_neck.region (s - η) D.epsilon⁻¹ =
                  D.end_neck.region (s - η) s ∧
                IsConnected (U ∩ interior K) ∧ IsConnected (U \ K) ∧
                (U ∩ interior K) ∪ (U \ K) = U \ frontier K ∧
                (∀ x ∈ U ∩ interior K,
                  connectedComponentIn (U \ frontier K) x = U ∩ interior K) ∧
                (∀ x ∈ U \ K, connectedComponentIn (U \ frontier K) x = U \ K) ∧
                ∀ L : Set M, IsCompact L → L ⊆ U →
                  ¬ U ∩ interior K ⊆ L ∧ ¬ U \ K ⊆ L := by
  obtain ⟨ε₁, hε₁, hsmall, hslice⟩ := exists_second_cap_essential_slice_threshold.{u}
  obtain ⟨ε₂, hε₂, -, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U hU hcU hend hfirst hDC hCD hcompact hencounter
  obtain ⟨s, hs, η, hη, hlo, hhi, hcollar, htail, hK, hKD, hcore,
      hfront, hunion, hinter, hescape⟩ :=
    hslice C D (hε.trans (min_le_left _ _)) hU hend hfirst hDC hCD hcompact hencounter
  have hlo' : -D.epsilon⁻¹ < s - η :=
    (neg_lt_zero.mpr (inv_pos.mpr D.epsilon_pos)).trans hlo
  obtain ⟨-, -, hint, -, -, -⟩ :=
    htrunc D (hε.trans (min_le_right _ _)) s ⟨by linarith, hs.2⟩
  obtain ⟨hcL, hcR, hcover, hcompL, hcompR⟩ :=
    D.truncated_sides_components hU hcU hK.isClosed hη hlo' hhi hcollar hint hfront
  exact ⟨s, hs, η, hη, hlo, hhi, hcollar, htail, hK, hKD, hcore, hfront,
    hunion, hinter, hcL, hcR, hcover, hcompL, hcompR, hescape⟩

end PoincareConjecture.CapCertificate
