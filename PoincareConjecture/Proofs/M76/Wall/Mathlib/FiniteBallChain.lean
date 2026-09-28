import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isFinitePLBallPair_finite_ball_chain
    (B T J Q : ℕ → Set E) (n : ℕ) {F₀ F₁ : Set E}
    (hB : ∀ i ≤ n, IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B i) (T i))
    (hJ : ∀ i < n, IsFinitePLBallPair (ℝ × ℝ) (J i) (Q i))
    (hcontact : ∀ i < n, B i ∩ B (i + 1) = J i)
    (hboundary : ∀ i < n, J i ⊆ T i ∧ J i ⊆ T (i + 1))
    (hfar : ∀ i ≤ n, ∀ j ≤ n, i + 1 < j → Disjoint (B i) (B j))
    (hjoints : ∀ i < n, ∀ j < n, i ≠ j → Disjoint (J i) (J j))
    (hF₀ : F₀ ⊆ T 0) (hF₁ : F₁ ⊆ T n)
    (hne₀ : F₀.Nonempty) (hne₁ : F₁.Nonempty)
    (havoid : ∀ i < n, Disjoint F₀ (J i) ∧ Disjoint F₁ (J i)) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (⋃ i ≤ n, B i)
      ((⋃ i ≤ n, T i) \ ⋃ i < n, J i \ Q i) ∧
      F₀ ⊆ ((⋃ i ≤ n, T i) \ ⋃ i < n, J i \ Q i) ∧
      F₁ ⊆ ((⋃ i ≤ n, T i) \ ⋃ i < n, J i \ Q i) := by
  let C : ℕ → Set E := fun k => ⋃ i ≤ k, B i
  let U : ℕ → Set E := fun k => ⋃ i < k, J i \ Q i
  let S : ℕ → Set E := fun k => (⋃ i ≤ k, T i) \ U k
  have hfirst (k : ℕ) (hk : k ≤ n) : F₀ ⊆ S k := by
    intro x hx
    refine ⟨mem_iUnion₂.mpr ⟨0, Nat.zero_le k, hF₀ hx⟩, ?_⟩
    intro hxU
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
    exact disjoint_left.mp (havoid i (hi.trans_le hk)).1 hx hxi.1
  have hlast : F₁ ⊆ S n := by
    intro x hx
    refine ⟨mem_iUnion₂.mpr ⟨n, le_rfl, hF₁ hx⟩, ?_⟩
    intro hxU
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
    exact disjoint_left.mp (havoid i hi).2 hx hxi.1
  have hprefix : ∀ k, k ≤ n → IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (C k) (S k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa [C, S, U] using hB 0 hk
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hk' : k ≤ n := by omega
      have hold := ih hk'
      have hnew := hB (k + 1) hk
      have hjoint := hJ k hkn
      have hjointOld : J k ⊆ S k := by
        intro x hx
        refine ⟨mem_iUnion₂.mpr ⟨k, le_rfl, (hboundary k hkn).1 hx⟩, ?_⟩
        intro hxU
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
        exact disjoint_left.mp
          (hjoints i (hi.trans hkn) k hkn (Nat.ne_of_lt hi)) hxi.1 hx
      have hcontact' : C k ∩ B (k + 1) = J k := by
        apply Subset.antisymm
        · rintro x ⟨hx, hxnew⟩
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          by_cases hik : i = k
          · exact (hcontact k hkn).subset ⟨hik ▸ hxi, hxnew⟩
          · exact False.elim (disjoint_left.mp
              (hfar i (hi.trans hk') (k + 1) hk (by omega)) hxi hxnew)
        · intro x hx
          have hi := (hcontact k hkn).symm.subset hx
          exact ⟨mem_iUnion₂.mpr ⟨k, le_rfl, hi.1⟩, hi.2⟩
      have houtOld : (S k \ J k).Nonempty := by
        obtain ⟨x, hx⟩ := hne₀
        exact ⟨x, hfirst k hk' hx,
          fun hxJ => disjoint_left.mp (havoid k hkn).1 hx hxJ⟩
      have houtNew : (T (k + 1) \ J k).Nonempty := by
        by_cases hnext : k + 1 < n
        · obtain ⟨x, hx, _⟩ := (hJ (k + 1) hnext).sdiff_nonempty
          refine ⟨x, (hboundary (k + 1) hnext).1 hx, ?_⟩
          exact fun hxJ => disjoint_left.mp
            (hjoints k hkn (k + 1) hnext (by omega)) hxJ hx
        · have hlastIndex : k + 1 = n := by omega
          obtain ⟨x, hx⟩ := hne₁
          refine ⟨x, ?_, fun hxJ => disjoint_left.mp (havoid k hkn).2 hx hxJ⟩
          rw [hlastIndex]
          exact hF₁ hx
      have hnewAvoid (x : E) (hx : x ∈ T (k + 1)) : x ∉ U k := by
        intro hxU
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
        have hin : i < n := hi.trans hkn
        have hxBi : x ∈ B i :=
          (hB i hin.le).1 ((hboundary i hin).1 hxi.1)
        exact disjoint_left.mp
          (hfar i hin.le (k + 1) hk (by omega)) hxBi (hnew.1 hx)
      have hcarrierStep : C (k + 1) = C k ∪ B (k + 1) := biUnion_le_succ B k
      have hboundaryStep : S (k + 1) =
          (S k \ (J k \ Q k)) ∪ (T (k + 1) \ (J k \ Q k)) := by
        have hU : U (k + 1) = U k ∪ (J k \ Q k) :=
          biUnion_lt_succ (fun i => J i \ Q i) k
        dsimp only [S]
        rw [biUnion_le_succ, hU]
        ext x
        have hx := hnewAvoid x
        simp only [mem_sdiff, mem_union]
        tauto
      rw [hcarrierStep, hboundaryStep]
      exact hold.union_of_actual_disk_contact hnew hjoint hjointOld
        (hboundary k hkn).2 houtOld houtNew hcontact'
  exact ⟨hprefix n le_rfl, hfirst n le_rfl, hlast⟩

end Set
