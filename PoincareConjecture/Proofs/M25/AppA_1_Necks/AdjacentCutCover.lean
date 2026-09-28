import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_adjacent_saturated_cut_cover
    (N N' : EpsilonNeck g) (hsep : N.IsSeparating)
    (hquarter : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hoverlap : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
    ∃ H : M → ℝ,
      Continuous H ∧
      (∀ x ∈ N.carrier, H x = (N.coordinate_inverse x).2) ∧
      (∀ x ∈ connectedComponent N.center \ N.carrier,
        H x = -N.epsilon⁻¹ ∨ H x = N.epsilon⁻¹) ∧
      (∀ x ∈ N'.carrier, -N.epsilon⁻¹ / 2 < H x) ∧
      (∀ x ∈ N'.carrier \ N.carrier, H x = N.epsilon⁻¹) ∧
      (∀ x y : M,
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
          |H x - H y|) ≤ g.edist x y) ∧
      ∀ a b : ℝ, N.epsilon⁻¹ / 2 < a → a < b → b < N.epsilon⁻¹ →
        let U := N.carrier ∩ H ⁻¹' Iio b
        let V := N'.carrier ∩ H ⁻¹' Ioi a
        IsOpen U ∧ IsOpen V ∧
        U ∪ V = N.carrier ∪ N'.carrier ∧
        U ∩ V = N.region a b ∧
        U = N.region (-N.epsilon⁻¹) b := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  obtain ⟨a₀, b₀, ha₀, hb₀, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  obtain ⟨H, hH, hinside, hnegative, hpositive, _, hdist⟩ :=
    N.exists_saturatedAxialHeight hsep a₀ b₀ ha₀ hb₀
  have houtside : ∀ x ∈ connectedComponent N.center \ N.carrier,
      H x = -N.epsilon⁻¹ ∨ H x = N.epsilon⁻¹ := by
    intro x hx
    rw [← hcover] at hx
    rcases hx.1 with (hn | hs) | hp
    · exact Or.inl (hnegative x ⟨hn, hx.2⟩)
    · exact False.elim (hx.2 (N.central_sphere_subset hs))
    · exact Or.inr (hpositive x ⟨hp, hx.2⟩)
  let q₀ := (N.coordinate_inverse N.center).1
  let p := N.coordinate_map (q₀, 3 * N.epsilon⁻¹ / 4)
  have hpheight : 3 * N.epsilon⁻¹ / 4 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith
  have hpold : p ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ _, hpheight⟩
  have hpcoord : (N.coordinate_inverse p).2 = 3 * N.epsilon⁻¹ / 4 := by
    exact congrArg Prod.snd (N.coordinate_inverse_map _ hpheight)
  have hpnew : p ∈ N'.carrier := by
    apply hquarter
    refine ⟨hpold, ?_, ?_⟩ <;> rw [hpcoord] <;> linarith
  have hnewK : N'.carrier ⊆ connectedComponent N.center := by
    intro x hx
    have hc := N'.isConnected_carrier.subset_connectedComponent hpnew hx
    rwa [← connectedComponent_eq (N.m25_carrier_subset_connectedComponent hpold)] at hc
  have hne : ∀ x ∈ N'.carrier, H x ≠ -N.epsilon⁻¹ / 2 := by
    intro x hx heq
    by_cases hxold : x ∈ N.carrier
    · have h := (hoverlap ⟨hxold, hx⟩).2.1
      rw [← hinside x hxold, heq] at h
      exact lt_irrefl _ h
    · rcases houtside x ⟨hnewK hx, hxold⟩ with hn | hp <;> linarith
  have hsign : ∀ x ∈ N'.carrier, -N.epsilon⁻¹ / 2 < H x := by
    intro x hx
    apply N'.isConnected_carrier.isPreconnected.lt_of_ne hH.continuousOn hne _ hx
    refine ⟨p, hpnew, ?_⟩
    rw [hinside p hpold, hpcoord]
    linarith
  have hnewOutside : ∀ x ∈ N'.carrier \ N.carrier, H x = N.epsilon⁻¹ := by
    intro x hx
    rcases houtside x ⟨hnewK hx.1, hx.2⟩ with hn | hp
    · have h := hsign x hx.1
      linarith
    · exact hp
  refine ⟨H, hH, hinside, houtside, hsign, hnewOutside, hdist, ?_⟩
  intro a b ha hab hb
  dsimp only
  refine ⟨N.carrier_open.inter (isOpen_Iio.preimage hH),
    N'.carrier_open.inter (isOpen_Ioi.preimage hH), ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx.1
    · rintro x (hx | hx)
      · by_cases hxlow : H x < b
        · exact Or.inl ⟨hx, hxlow⟩
        · have hxhigh : b ≤ H x := le_of_not_gt hxlow
          have hxquarter : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
            refine ⟨hx, ?_, (N.coordinate_inverse_mem x hx).2.2⟩
            rw [← hinside x hx]
            linarith
          exact Or.inr ⟨hquarter hxquarter, by change a < H x; linarith⟩
      · by_cases hxhigh : a < H x
        · exact Or.inr ⟨hx, hxhigh⟩
        · have hxlow : H x ≤ a := le_of_not_gt hxhigh
          have hxold : x ∈ N.carrier := by
            by_contra hnot
            have h := hnewOutside x ⟨hx, hnot⟩
            linarith
          exact Or.inl ⟨hxold, by change H x < b; linarith⟩
  · ext x
    constructor
    · rintro ⟨⟨hx, hxb⟩, _, hxa⟩
      exact ⟨hx, by simpa only [mem_preimage, mem_Ioi, hinside x hx] using hxa,
        by simpa only [mem_preimage, mem_Iio, hinside x hx] using hxb⟩
    · intro hx
      have hxnew : x ∈ N'.carrier :=
        hquarter ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩
      exact ⟨⟨hx.1, by simpa only [mem_preimage, mem_Iio, hinside x hx.1] using hx.2.2⟩,
        hxnew, by simpa only [mem_preimage, mem_Ioi, hinside x hx.1] using hx.2.1⟩
  · ext x
    constructor
    · rintro ⟨hx, hxb⟩
      exact ⟨hx, (N.coordinate_inverse_mem x hx).2.1,
        by simpa only [mem_preimage, mem_Iio, hinside x hx] using hxb⟩
    · intro hx
      exact ⟨hx.1, by simpa only [mem_preimage, mem_Iio, hinside x hx.1] using hx.2.2⟩

end PoincareConjecture.EpsilonNeck
