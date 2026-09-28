import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.FiniteFrontier














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)



theorem frontier_endpoint_of_mem_closure {i : ℤ} (hi : i ∈ C.shape.active)
    {x : M}
    (hfront : x ∈ frontier (⋃ j : {j // j ∈ C.shape.active}, (C.neck j.1).carrier))
    (hclosure : x ∈ closure (C.neck i).carrier) :
    (i - 1 ∉ C.shape.active ∧
      x ∈ closure ((C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2))) ∨
    (i + 1 ∉ C.shape.active ∧
      x ∈ closure ((C.neck i).region (ε⁻¹ / 2) ε⁻¹)) := by
  have hout (j : ℤ) (hj : j ∈ C.shape.active) : x ∉ (C.neck j).carrier := by
    intro hxj
    have hU := isOpen_iUnion fun k : {k // k ∈ C.shape.active} =>
      (C.neck k.1).carrier_open
    exact (hU.frontier_eq ▸ hfront).2 (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)
  have hfronti : x ∈ frontier (C.neck i).carrier := by
    rw [(C.neck i).carrier_open.frontier_eq]
    exact ⟨hclosure, hout i hi⟩
  have hie : (C.neck i).epsilon = ε := C.epsilon_eq i hi
  have he : 0 < ε⁻¹ := by
    rw [← hie]
    exact inv_pos.mpr (C.neck i).epsilon_pos
  have hend := (C.neck i).frontier_subset_closure_ends
    (a := -ε⁻¹ / 2) (b := ε⁻¹ / 2)
    (by rw [hie]; linarith) (by rw [hie]; linarith) hfronti
  simp only [hie, mem_union] at hend
  rcases hend with hneg | hpos
  · refine Or.inl ⟨?_, hneg⟩
    intro hp
    have hn : i - 1 + 1 ∈ C.shape.active := by simpa using hi
    have hquarters := C.overlap_contains_quarters (i - 1) hp hn
    have hwithin := C.overlap_within_three_quarters (i - 1) hp hn
    simp only [sub_add_cancel] at hquarters hwithin
    have hcapture := (C.neck (i - 1)).closure_negative_quarter_diff_carrier_subset
      (C.neck i)
      (by simpa only [C.epsilon_eq (i - 1) hp] using hquarters.1)
      (by simpa only [hie] using hquarters.2)
      (by simpa only [C.epsilon_eq (i - 1) hp, hie] using hwithin)
    exact hout (i - 1) hp
      (hcapture ⟨by simpa only [hie] using hneg, hout i hi⟩)
  · refine Or.inr ⟨?_, hpos⟩
    intro hn
    have hquarters := C.overlap_contains_quarters i hi hn
    have hwithin := C.overlap_within_three_quarters i hi hn
    have hcapture := (C.neck i).closure_positive_quarter_diff_carrier_subset
      (C.neck (i + 1))
      (by simpa only [hie] using hquarters.1)
      (by simpa only [C.epsilon_eq (i + 1) hn] using hquarters.2)
      (by simpa only [hie, C.epsilon_eq (i + 1) hn] using hwithin)
    exact hout (i + 1) hn
      (hcapture ⟨by simpa only [hie] using hpos, hout i hi⟩)



theorem frontier_inter_iUnion_closure_subset_outer_ends :
    frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ∩
        (⋃ i : {i // i ∈ C.shape.active}, closure (C.neck i.1).carrier) ⊆
      match C.shape with
      | .finite a b => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)) ∪
          closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .forward a => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2))
      | .backward b => closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .biInfinite => ∅ := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx.2
  rcases C.frontier_endpoint_of_mem_closure i.2 hx.1 hi with
    ⟨hprev, hneg⟩ | ⟨hnext, hpos⟩
  · cases hshape : C.shape with
    | finite a b =>
      have hiab : a ≤ i.1 ∧ i.1 ≤ b := by simpa [hshape, ChainShape.active] using i.2
      have hia : i.1 = a := by
        by_contra hia
        apply hprev
        simp only [hshape, ChainShape.active, mem_Icc]
        omega
      exact Or.inl (hia ▸ hneg)
    | forward a =>
      have hia : i.1 = a := by
        have hi' : a ≤ i.1 := by simpa [hshape, ChainShape.active] using i.2
        by_contra hia
        apply hprev
        simp only [hshape, ChainShape.active, mem_Ici]
        omega
      simpa only [hshape, hia] using hneg
    | backward b =>
      exfalso
      apply hprev
      have hi' : i.1 ≤ b := by simpa [hshape, ChainShape.active] using i.2
      simp only [hshape, ChainShape.active, mem_Iic]
      omega
    | biInfinite =>
      exact (hprev (by simp [hshape, ChainShape.active])).elim
  · cases hshape : C.shape with
    | finite a b =>
      have hiab : a ≤ i.1 ∧ i.1 ≤ b := by simpa [hshape, ChainShape.active] using i.2
      have hib : i.1 = b := by
        by_contra hib
        apply hnext
        simp only [hshape, ChainShape.active, mem_Icc]
        omega
      exact Or.inr (hib ▸ hpos)
    | forward a =>
      exfalso
      apply hnext
      have hi' : a ≤ i.1 := by simpa [hshape, ChainShape.active] using i.2
      simp only [hshape, ChainShape.active, mem_Ici]
      omega
    | backward b =>
      have hib : i.1 = b := by
        have hi' : i.1 ≤ b := by simpa [hshape, ChainShape.active] using i.2
        by_contra hib
        apply hnext
        simp only [hshape, ChainShape.active, mem_Iic]
        omega
      simpa only [hshape, hib] using hpos
    | biInfinite =>
      exact (hnext (by simp [hshape, ChainShape.active])).elim



theorem disjoint_frontier_closure_of_neighbors {i : ℤ} (hi : i ∈ C.shape.active)
    (hprev : i - 1 ∈ C.shape.active) (hnext : i + 1 ∈ C.shape.active) :
    Disjoint (frontier (⋃ j : {j // j ∈ C.shape.active}, (C.neck j.1).carrier))
      (closure (C.neck i).carrier) := by
  apply disjoint_left.mpr
  intro x hx hxi
  rcases C.frontier_endpoint_of_mem_closure hi hx hxi with h | h
  · exact h.1 hprev
  · exact h.1 hnext

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


private theorem eventually_index_not_mem_finite_of_tendsto
    {ι : Type*} {l : Filter ι} {p : ι → M} {f : ι → ℤ} {x : M}
    (htendsto : Tendsto p l (𝓝 x))
    (hmem : ∀ᶠ n in l, p n ∈ (C.neck (f n)).carrier)
    (hout : ∀ i ∈ C.shape.active, x ∉ closure (C.neck i).carrier)
    {J : Set ℤ} (hJ : J.Finite) (hactive : J ⊆ C.shape.active) :
    ∀ᶠ n in l, f n ∉ J := by
  have hclosed : IsClosed (⋃ i ∈ J, closure (C.neck i).carrier) :=
    hJ.isClosed_biUnion (fun _ _ => isClosed_closure)
  have hx : x ∉ ⋃ i ∈ J, closure (C.neck i).carrier := by
    intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hout i (hactive hi) hxi
  filter_upwards [htendsto.eventually (hclosed.isOpen_compl.mem_nhds hx), hmem] with
    n hn hpn hf
  exact hn (mem_iUnion₂.mpr ⟨f n, hf, subset_closure hpn⟩)



theorem eventually_index_not_mem_finite_of_tendsto_frontier
    {ι : Type*} {l : Filter ι} {p : ι → M} {f : ι → ℤ} {x : M}
    (htendsto : Tendsto p l (𝓝 x))
    (hmem : ∀ᶠ n in l, p n ∈ (C.neck (f n)).carrier)
    (hfront : x ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier))
    (houter : x ∉ match C.shape with
      | .finite a b => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)) ∪
          closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .forward a => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2))
      | .backward b => closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .biInfinite => ∅)
    {J : Set ℤ} (hJ : J.Finite) (hactive : J ⊆ C.shape.active) :
    ∀ᶠ n in l, f n ∉ J := by
  apply C.eventually_index_not_mem_finite_of_tendsto htendsto hmem _ hJ hactive
  intro i hi hxi
  exact houter (C.frontier_inter_iUnion_closure_subset_outer_ends
    ⟨hfront, mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩⟩)



theorem tendsto_indices_atTop_of_tendsto_forward_frontier
    {a : ℤ} (hshape : C.shape = .forward a)
    {ι : Type*} {l : Filter ι} {p : ι → M} {f : ι → ℤ} {x : M}
    (htendsto : Tendsto p l (𝓝 x))
    (hmem : ∀ᶠ n in l, p n ∈ (C.neck (f n)).carrier)
    (hactive : ∀ᶠ n in l, f n ∈ C.shape.active)
    (hfront : x ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier))
    (houter : x ∉ closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2))) :
    Tendsto f l atTop := by
  apply tendsto_atTop.2
  intro b
  have hescape := C.eventually_index_not_mem_finite_of_tendsto_frontier
    htendsto hmem hfront (by simpa only [hshape] using houter)
    (J := Icc a b) (finite_Icc a b) (by
      intro i hi
      simpa only [hshape, ChainShape.active, mem_Ici] using hi.1)
  filter_upwards [hescape, hactive] with n hn hna
  have hna' : a ≤ f n := by simpa only [hshape, ChainShape.active, mem_Ici] using hna
  have hgt : b < f n := by
    by_contra h
    exact hn ⟨hna', le_of_not_gt h⟩
  exact hgt.le


theorem tendsto_indices_atBot_of_tendsto_backward_frontier
    {b : ℤ} (hshape : C.shape = .backward b)
    {ι : Type*} {l : Filter ι} {p : ι → M} {f : ι → ℤ} {x : M}
    (htendsto : Tendsto p l (𝓝 x))
    (hmem : ∀ᶠ n in l, p n ∈ (C.neck (f n)).carrier)
    (hactive : ∀ᶠ n in l, f n ∈ C.shape.active)
    (hfront : x ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier))
    (houter : x ∉ closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)) :
    Tendsto f l atBot := by
  apply tendsto_atBot.2
  intro a
  have hescape := C.eventually_index_not_mem_finite_of_tendsto_frontier
    htendsto hmem hfront (by simpa only [hshape] using houter)
    (J := Icc a b) (finite_Icc a b) (by
      intro i hi
      simpa only [hshape, ChainShape.active, mem_Iic] using hi.2)
  filter_upwards [hescape, hactive] with n hn hnb
  have hnb' : f n ≤ b := by simpa only [hshape, ChainShape.active, mem_Iic] using hnb
  have hlt : f n < a := by
    by_contra h
    exact hn ⟨le_of_not_gt h, hnb'⟩
  exact hlt.le

end PoincareConjecture.BalancedNeckChain
