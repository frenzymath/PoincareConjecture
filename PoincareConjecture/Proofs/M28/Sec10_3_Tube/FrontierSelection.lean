import Mathlib.Topology.Order.Compact
import Mathlib.Data.List.Chain
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace PoincareConjecture.M28

variable {X : Type*} [TopologicalSpace X]

theorem exists_finite_frontier_selection
    (γ : ℝ → X) (V : ℝ → Set X) {a b d : ℝ}
    (hab : a ≤ b) (hd : 0 < d) (hγ : ContinuousOn γ (Icc a b))
    (hopen : ∀ s ∈ Icc a b, IsOpen (V s))
    (hnear : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |t - s| < d → γ t ∈ V s) :
    ∃ l : List ℝ,
      (∀ s ∈ a :: l, s ∈ Icc a b) ∧
      (a :: l).IsChain (fun s t =>
        d ≤ t - s ∧ γ t ∈ frontier (V s) ∧ MapsTo γ (Ico s t) (V s)) ∧
      MapsTo γ (Icc ((a :: l).getLast (List.cons_ne_nil _ _)) b)
        (V ((a :: l).getLast (List.cons_ne_nil _ _))) := by
  classical
  have hbounded : ∀ n : ℕ, ∀ c ∈ Icc a b, b - c < (n : ℝ) * d →
      ∃ l : List ℝ,
        (∀ s ∈ c :: l, s ∈ Icc a b) ∧
        (c :: l).IsChain (fun s t =>
          d ≤ t - s ∧ γ t ∈ frontier (V s) ∧ MapsTo γ (Ico s t) (V s)) ∧
        MapsTo γ (Icc ((c :: l).getLast (List.cons_ne_nil _ _)) b)
          (V ((c :: l).getLast (List.cons_ne_nil _ _))) := by
    intro n
    induction n with
    | zero =>
      intro c hc hbudget
      norm_num at hbudget
      exact (not_lt_of_ge hc.2 hbudget).elim
    | succ n ih =>
      intro c hc hbudget
      by_cases hstop : MapsTo γ (Icc c b) (V c)
      · refine ⟨[], ?_, List.IsChain.singleton _, ?_⟩
        · simpa only [List.mem_singleton, forall_eq] using hc
        · simpa only [List.getLast_singleton] using hstop
      · have hex : ∃ t ∈ Icc c b, γ t ∉ V c := by
          by_contra h
          apply hstop
          intro t ht
          by_contra htout
          exact h ⟨t, ht, htout⟩
        let K : Set ℝ := Icc c b ∩ γ ⁻¹' (V c)ᶜ
        have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
          ((hγ.mono (Icc_subset_Icc hc.1 le_rfl)).preimage_isClosed_of_isClosed
            isClosed_Icc (hopen c hc).isClosed_compl) inter_subset_left
        obtain ⟨t, ht, htout⟩ := hex
        obtain ⟨s, hs, hleast⟩ := hK.exists_isLeast ⟨t, ht, htout⟩
        have hsab : s ∈ Icc a b := ⟨hc.1.trans hs.1.1, hs.1.2⟩
        have hgap : d ≤ s - c := by
          by_contra h
          apply hs.2
          apply hnear c hc s hsab
          rw [abs_of_nonneg (sub_nonneg.mpr hs.1.1)]
          exact lt_of_not_ge h
        have hcs : c < s := by linarith
        have hprefix : MapsTo γ (Ico c s) (V c) := by
          intro t ht
          by_contra hout
          have hst : s ≤ t := hleast ⟨⟨ht.1, ht.2.le.trans hs.1.2⟩, hout⟩
          exact (not_lt_of_ge hst) ht.2
        have hclosed : MapsTo γ (Icc c s) (closure (V c)) := by
          have hγcs : ContinuousOn γ (closure (Ico c s)) := by
            rw [closure_Ico hcs.ne]
            exact hγ.mono (Icc_subset_Icc hc.1 hs.1.2)
          simpa only [closure_Ico hcs.ne] using
            hprefix.closure_of_continuousOn hγcs
        have hfront : γ s ∈ frontier (V c) := by
          rw [frontier, (hopen c hc).interior_eq]
          exact ⟨hclosed (right_mem_Icc.mpr hcs.le), hs.2⟩
        have hremaining : b - s < (n : ℝ) * d := by
          push_cast at hbudget
          nlinarith
        obtain ⟨l, hlmem, hlchain, hlast⟩ := ih s hsab hremaining
        refine ⟨s :: l, ?_, ?_, ?_⟩
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hc
          · exact hlmem t ht
        · exact List.isChain_cons_cons.mpr ⟨⟨hgap, hfront, hprefix⟩, hlchain⟩
        · simpa only [List.getLast_cons_cons] using hlast
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / d)
  exact hbounded n a (left_mem_Icc.mpr hab) ((div_lt_iff₀ hd).mp hn)

omit [TopologicalSpace X] in

theorem mapsTo_finite_frontier_selection
    {γ : ℝ → X} {V : ℝ → Set X} {a b : ℝ} {l : List ℝ}
    (hchain : (a :: l).IsChain (fun s t => MapsTo γ (Ico s t) (V s)))
    (hlast : MapsTo γ (Icc ((a :: l).getLast (List.cons_ne_nil _ _)) b)
      (V ((a :: l).getLast (List.cons_ne_nil _ _)))) :
    MapsTo γ (Icc a b) {x | ∃ s ∈ a :: l, x ∈ V s} := by
  induction l generalizing a with
  | nil =>
    intro t ht
    exact ⟨a, by simp, by simpa only [List.getLast_singleton] using hlast ht⟩
  | cons c l ih =>
    obtain ⟨hfirst, htail⟩ := List.isChain_cons_cons.mp hchain
    intro t ht
    by_cases htc : t < c
    · exact ⟨a, List.mem_cons_self, hfirst ⟨ht.1, htc⟩⟩
    · have htailLast : MapsTo γ (Icc ((c :: l).getLast (List.cons_ne_nil _ _)) b)
          (V ((c :: l).getLast (List.cons_ne_nil _ _))) := by
        simpa only [List.getLast_cons_cons] using hlast
      obtain ⟨s, hs, hx⟩ := ih htail htailLast ⟨le_of_not_gt htc, ht.2⟩
      exact ⟨s, List.mem_cons_of_mem _ hs, hx⟩

end PoincareConjecture.M28
