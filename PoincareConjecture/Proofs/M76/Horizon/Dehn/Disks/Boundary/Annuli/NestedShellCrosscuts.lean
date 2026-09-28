import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn

theorem exists_first_exit_parameter {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) (f : ℝ → X) (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) (hzero : f 0 ∈ U) (hend : f T ∉ U) :
    ∃ t ∈ Ioc (0 : ℝ) T, f t ∈ frontier U ∧ MapsTo f (Ico 0 t) U := by
  let A := Icc (0 : ℝ) T ∩ f ⁻¹' Uᶜ
  have hA : IsCompact A := isCompact_Icc.inter_right (hU.isClosed_compl.preimage hf)
  obtain ⟨t, ht, hleast⟩ := hA.exists_isLeast ⟨T, ⟨hT.le, le_rfl⟩, hend⟩
  have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (by
    intro heq
    exact ht.2 (heq ▸ hzero))
  have hbefore : MapsTo f (Ico 0 t) U := by
    intro s hs
    by_contra hnot
    exact (not_le_of_gt hs.2) (hleast ⟨⟨hs.1, hs.2.le.trans ht.1.2⟩, hnot⟩)
  refine ⟨t, ⟨htpos, ht.1.2⟩, ?_, hbefore⟩
  refine ⟨?_, fun hi ↦ ht.2 (interior_subset hi)⟩
  apply closure_mono hbefore.image_subset
  apply mem_closure_image hf.continuousAt
  rw [closure_Ico htpos.ne]
  exact ⟨htpos.le, le_rfl⟩

theorem exists_horizontal_support_points {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hne : (interior S).Nonempty) :
    ∃ a ∈ frontier S, ∃ b ∈ frontier S, a.1 < b.1 ∧
      ∀ z ∈ S, a.1 ≤ z.1 ∧ z.1 ≤ b.1 := by
  have hSne : S.Nonempty := hne.mono interior_subset
  obtain ⟨a, ha, hmin⟩ := hS.exists_isMinOn hSne continuous_fst.continuousOn
  obtain ⟨b, hb, hmax⟩ := hS.exists_isMaxOn hSne continuous_fst.continuousOn
  have hbounds : ∀ z ∈ S, a.1 ≤ z.1 ∧ z.1 ≤ b.1 := fun z hz ↦ ⟨hmin hz, hmax hz⟩
  have hopen : IsOpen (Prod.fst '' interior S) := isOpenMap_fst _ isOpen_interior
  have hsub : Prod.fst '' interior S ⊆ Icc a.1 b.1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hbounds w (interior_subset hw)
  have hstrict : ∀ z ∈ interior S, a.1 < z.1 ∧ z.1 < b.1 := by
    intro z hz
    have hh := interior_maximal hsub hopen (mem_image_of_mem Prod.fst hz)
    simpa only [interior_Icc, mem_Ioo] using hh
  obtain ⟨z, hz⟩ := hne
  refine ⟨a, ⟨subset_closure ha, ?_⟩, b, ⟨subset_closure hb, ?_⟩,
    ((hstrict z hz).1.trans (hstrict z hz).2), hbounds⟩
  · exact fun hi ↦ (lt_irrefl a.1) (hstrict a hi).1
  · exact fun hi ↦ (lt_irrefl b.1) (hstrict b hi).2

theorem exists_nested_horizontal_crosscuts {S T : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hSne : (interior S).Nonempty) (hT : IsCompact T)
    (hST : S ⊆ interior T) :
    ∃ a ∈ frontier S, ∃ b ∈ frontier S, ∃ l r : ℝ,
      0 < l ∧ 0 < r ∧ a.1 < b.1 ∧
      (a.1 - l, a.2) ∈ frontier T ∧ (b.1 + r, b.2) ∈ frontier T ∧
      (∀ u ∈ Ico (0 : ℝ) l, (a.1 - u, a.2) ∈ interior T) ∧
      (∀ u ∈ Ico (0 : ℝ) r, (b.1 + u, b.2) ∈ interior T) ∧
      (∀ u : ℝ, 0 < u → (a.1 - u, a.2) ∉ S) ∧
      (∀ u : ℝ, 0 < u → (b.1 + u, b.2) ∉ S) ∧
      Disjoint ((fun u : ℝ ↦ (a.1 - u, a.2)) '' Icc 0 l)
        ((fun u : ℝ ↦ (b.1 + u, b.2)) '' Icc 0 r) := by
  obtain ⟨a, ha, b, hb, hab, hbounds⟩ := exists_horizontal_support_points hS hSne
  have haS := hS.isClosed.frontier_subset ha
  have hbS := hS.isClosed.frontier_subset hb
  obtain ⟨M, hM, hbound⟩ := hT.isBounded.exists_pos_norm_le
  let L := M + |a.1| + 1
  let R := M + |b.1| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hleft : (a.1 - L, a.2) ∉ interior T := by
    intro hx
    have hh := (norm_fst_le (a.1 - L, a.2)).trans (hbound _ (interior_subset hx))
    rw [Real.norm_eq_abs] at hh
    have ha' := le_abs_self a.1
    have hh' := neg_le_abs (a.1 - L)
    dsimp [L] at *
    linarith
  have hright : (b.1 + R, b.2) ∉ interior T := by
    intro hx
    have hh := (norm_fst_le (b.1 + R, b.2)).trans (hbound _ (interior_subset hx))
    rw [Real.norm_eq_abs] at hh
    have hb' := neg_le_abs b.1
    have hh' := le_abs_self (b.1 + R)
    dsimp [R] at *
    linarith
  obtain ⟨l, hl, hlfront, hlbefore⟩ := exists_first_exit_parameter isOpen_interior
    (fun u : ℝ ↦ (a.1 - u, a.2)) (by fun_prop) hL (by simpa using hST haS) hleft
  obtain ⟨r, hr, hrfront, hrbefore⟩ := exists_first_exit_parameter isOpen_interior
    (fun u : ℝ ↦ (b.1 + u, b.2)) (by fun_prop) hR (by simpa using hST hbS) hright
  have hfront : frontier (interior T) ⊆ frontier T := frontier_interior_subset
  refine ⟨a, ha, b, hb, l, r, hl.1, hr.1, hab, hfront hlfront, hfront hrfront,
    hlbefore, hrbefore, ?_, ?_, ?_⟩
  · intro u hu hx
    have hh := (hbounds _ hx).1
    dsimp at hh
    linarith
  · intro u hu hx
    have hh := (hbounds _ hx).2
    dsimp at hh
    linarith
  · apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, heq⟩
    have hh := congrArg Prod.fst heq
    dsimp at hh
    linarith [hu.1, hv.1]

end PoincareConjecture.M76.Dehn
