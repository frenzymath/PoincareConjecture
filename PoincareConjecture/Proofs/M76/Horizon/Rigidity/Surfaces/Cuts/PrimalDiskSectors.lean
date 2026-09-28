import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalDiskSpokes
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusMarkedRectangle

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

open PeriodicSquare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def CyclicFourArcPartition (q : Set E) (a b c d : E) : Prop :=
  ∃ A B C D : Set E,
    IsFinitePLBallPair ℝ A {a, b} ∧ IsFinitePLBallPair ℝ B {b, c} ∧
    IsFinitePLBallPair ℝ C {c, d} ∧ IsFinitePLBallPair ℝ D {d, a} ∧
    (A ∪ B) ∪ (C ∪ D) = q ∧
    A ∩ B = {b} ∧ B ∩ C = {c} ∧ C ∩ D = {d} ∧ D ∩ A = {a} ∧
    Disjoint A C ∧ Disjoint B D

private theorem exists_three_boundary_arcs
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    {a b c : E} (ha : a ∈ q) (hb : b ∈ q) (hc : c ∈ q)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ A B C : Set E,
      IsFinitePLBallPair ℝ A {a, b} ∧ IsFinitePLBallPair ℝ B {b, c} ∧
      IsFinitePLBallPair ℝ C {c, a} ∧ (A ∪ B) ∪ C = q ∧
      A ∩ B = {b} ∧ B ∩ C = {c} ∧ C ∩ A = {a} := by
  obtain ⟨U, V, hU, hV, huv, hiv⟩ := hd.exists_boundary_arcs ha hc hac
  have hbuv : b ∈ U ∪ V := huv.symm ▸ hb
  have oriented : ∃ U V : Set E,
      IsFinitePLBallPair ℝ U {a, c} ∧ IsFinitePLBallPair ℝ V {a, c} ∧
      U ∪ V = q ∧ U ∩ V = {a, c} ∧ b ∈ U := by
    rcases hbuv with hbU | hbV
    · exact ⟨U, V, hU, hV, huv, hiv, hbU⟩
    · exact ⟨V, U, hV, hU, by rw [union_comm]; exact huv,
        by rw [inter_comm]; exact hiv, hbV⟩
  obtain ⟨U, V, hU, hV, huv, hiv, hbU⟩ := oriented
  obtain ⟨A, B, hA, hB, habU, habI, hcA, haB⟩ :=
    exists_split_interval_at hU hbU hac hab hbc
  have hAU : A ⊆ U := by rw [← habU]; exact subset_union_left
  have hBU : B ⊆ U := by rw [← habU]; exact subset_union_right
  have cross {x : E} (hxU : x ∈ U) (hxV : x ∈ V) : x = a ∨ x = c := by
    simpa only [mem_insert_iff, mem_singleton_iff] using hiv.subset ⟨hxU, hxV⟩
  refine ⟨A, B, V, hA, hB, by simpa only [pair_comm c a] using hV,
    by rw [habU, huv], habI, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      rcases cross (hBU hx.1) hx.2 with rfl | rfl
      · exact (haB hx.1).elim
      · simp
    · rintro x rfl
      exact ⟨hB.1 (by simp), hV.1 (by simp)⟩
  · apply Subset.antisymm
    · intro x hx
      rcases cross (hAU hx.2) hx.1 with rfl | rfl
      · simp
      · exact (hcA hx.2).elim
    · rintro x rfl
      exact ⟨hV.1 (by simp), hA.1 (by simp)⟩

private theorem split_three_boundary_arcs
    {q A B C : Set E} {a b c d : E}
    (hA : IsFinitePLBallPair ℝ A {a, b}) (hB : IsFinitePLBallPair ℝ B {b, c})
    (hC : IsFinitePLBallPair ℝ C {c, a})
    (hcover : (A ∪ B) ∪ C = q) (hAB : A ∩ B = {b})
    (hBC : B ∩ C = {c}) (hCA : C ∩ A = {a})
    (hd : d ∈ A) (hab : a ≠ b) (had : a ≠ d) (hdb : d ≠ b) :
    CyclicFourArcPartition q a d b c := by
  obtain ⟨U, V, hU, hV, huv, hiv, hbU, haV⟩ :=
    exists_split_interval_at hA hd hab had hdb
  have hUA : U ⊆ A := by rw [← huv]; exact subset_union_left
  have hVA : V ⊆ A := by rw [← huv]; exact subset_union_right
  refine ⟨U, V, B, C, hU, hV, hB, hC, ?_, hiv, ?_, hBC, ?_, ?_, ?_⟩
  · rw [huv, ← union_assoc, hcover]
  · apply Subset.antisymm
    · exact fun x hx ↦ hAB.subset ⟨hVA hx.1, hx.2⟩
    · rintro x rfl
      exact ⟨hV.1 (by simp), hB.1 (by simp)⟩
  · apply Subset.antisymm
    · exact fun x hx ↦ hCA.subset ⟨hx.1, hUA hx.2⟩
    · rintro x rfl
      exact ⟨hC.1 (by simp), hU.1 (by simp)⟩
  · apply disjoint_left.mpr
    intro x hxU hxB
    have heq : x = b := hAB.subset ⟨hUA hxU, hxB⟩
    exact hbU (heq ▸ hxU)
  · apply disjoint_left.mpr
    intro x hxV hxC
    have heq : x = a := hCA.subset ⟨hxC, hVA hxV⟩
    exact haV (heq ▸ hxV)

theorem exists_four_prescribed_rim_arcs
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (marks : Fin 4 → E) (hm : Function.Injective marks) (hq : ∀ i, marks i ∈ q) :
    ∃ σ : Fin 4 ≃ Fin 4,
      CyclicFourArcPartition q (marks (σ 0)) (marks (σ 1)) (marks (σ 2)) (marks (σ 3)) := by
  have hne {i j : Fin 4} (h : i ≠ j) : marks i ≠ marks j := fun he ↦ h (hm he)
  obtain ⟨A, B, C, hA, hB, hC, hcover, hAB, hBC, hCA⟩ :=
    exists_three_boundary_arcs hd (hq 0) (hq 2) (hq 1)
      (hne (by decide)) (hne (by decide)) (hne (by decide))
  have hthree : marks 3 ∈ (A ∪ B) ∪ C := hcover.symm ▸ hq 3
  rcases hthree with (h3 | h3) | h3
  · let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective ![0, 3, 2, 1] (by decide)
    refine ⟨σ, ?_⟩
    exact split_three_boundary_arcs hA hB hC hcover hAB hBC hCA h3
      (hne (by decide)) (hne (by decide)) (hne (by decide))
  · let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective ![2, 3, 1, 0] (by decide)
    refine ⟨σ, ?_⟩
    have hc : (B ∪ C) ∪ A = q := by
      calc
        (B ∪ C) ∪ A = (A ∪ B) ∪ C := by ext x; simp only [mem_union]; tauto
        _ = q := hcover
    exact split_three_boundary_arcs hB hC hA hc hBC hCA hAB h3
      (hne (by decide)) (hne (by decide)) (hne (by decide))
  · let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective ![1, 3, 0, 2] (by decide)
    refine ⟨σ, ?_⟩
    have hc : (C ∪ A) ∪ B = q := by
      calc
        (C ∪ A) ∪ B = (A ∪ B) ∪ C := by ext x; simp only [mem_union]; tauto
        _ = q := hcover
    exact split_three_boundary_arcs hC hA hB hc hCA hAB hBC h3
      (hne (by decide)) (hne (by decide)) (hne (by decide))

end PoincareConjecture.M76.OriginalTriangleCopies
