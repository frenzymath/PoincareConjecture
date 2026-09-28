import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace PoincareConjecture.M76.Dehn.Annuli

variable {C : Type*}

def twoBandGraph (r : Bool → Bool → C) : SimpleGraph C where
  Adj c d := c ≠ d ∧ ∃ b s, r b s = c ∧ r b (!s) = d
  symm := ⟨by
    rintro c d ⟨hne, b, s, hc, hd⟩
    exact ⟨hne.symm, b, !s, hd, by simpa using hc⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

theorem exists_shared_component_of_twoBandGraph_connected
    (r : Bool → Bool → C) (hconn : (twoBandGraph r).Connected) :
    ∃ s t, r false s = r true t := by
  by_contra hnot
  have hne (s t : Bool) : r false s ≠ r true t :=
    fun h ↦ hnot ⟨s, t, h⟩
  have hadj {c d : C} (h : (twoBandGraph r).Adj c d) :
      (∃ s, r false s = c) ↔ ∃ s, r false s = d := by
    obtain ⟨_, b, s, rfl, rfl⟩ := h
    cases b
    · exact ⟨fun _ ↦ ⟨!s, rfl⟩, fun _ ↦ ⟨s, rfl⟩⟩
    · exact ⟨fun ⟨t, ht⟩ ↦ False.elim (hne t s ht),
        fun ⟨t, ht⟩ ↦ False.elim (hne t (!s) ht)⟩
  have hwalk {c d : C} (p : (twoBandGraph r).Walk c d) :
      (∃ s, r false s = c) ↔ ∃ s, r false s = d := by
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj h).trans ih
  obtain ⟨p⟩ := hconn.preconnected (r false false) (r true false)
  obtain ⟨s, hs⟩ := (hwalk p).mp ⟨false, rfl⟩
  exact hne s false hs

open Classical in
noncomputable def componentRims (r : Bool → Bool → C) (c : C) : Finset (Bool × Bool) :=
  Finset.univ.filter (fun z ↦ r z.1 z.2 = c)

theorem exists_two_rim_count_zero_component [Fintype C]
    (r : Bool → Bool → C) (hconn : (twoBandGraph r).Connected)
    (hcover : ∀ c, ∃ b s, r b s = c) (χ : C → ℤ)
    (hbound : ∀ c, χ c ≤ 2 - ((componentRims r c).card : ℤ))
    (hnodisk : ∀ c, (componentRims r c).card = 1 → χ c ≠ 1)
    (htotal : 0 ≤ ∑ c, χ c) :
    (∀ c, χ c = 0) ∧ ∃ c s t, χ c = 0 ∧ r false s = c ∧ r true t = c ∧
      componentRims r c = {(false, s), (true, t)} := by
  classical
  have hpositive (c : C) : 0 < (componentRims r c).card := by
    obtain ⟨b, s, hbs⟩ := hcover c
    exact Finset.card_pos.mpr ⟨(b, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbs⟩⟩
  have hnonpos (c : C) : χ c ≤ 0 := by
    have hb := hbound c
    have hp := hpositive c
    by_cases hcard : (componentRims r c).card = 1
    · have hn := hnodisk c hcard
      omega
    · omega
  have hsum : ∑ c, χ c = 0 :=
    le_antisymm (Finset.sum_nonpos (fun c _ ↦ hnonpos c)) htotal
  have hzero (c : C) : χ c = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun c _ ↦ hnonpos c)).mp hsum c (Finset.mem_univ _)
  obtain ⟨s, t, hst⟩ := exists_shared_component_of_twoBandGraph_connected r hconn
  let c := r false s
  have hpair : {(false, s), (true, t)} ⊆ componentRims r c := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst.symm⟩
  have hcard : (componentRims r c).card ≤ 2 := by
    have hb := hbound c
    rw [hzero] at hb
    omega
  have heq : componentRims r c = {(false, s), (true, t)} := by
    apply (Finset.eq_of_subset_of_card_le hpair ?_).symm
    have hne : (false, s) ≠ (true, t) := by
      intro h
      have := congrArg Prod.fst h
      cases this
    simpa only [Finset.card_pair hne] using hcard
  exact ⟨hzero, c, s, t, hzero c, rfl, hst.symm, heq⟩

end PoincareConjecture.M76.Dehn.Annuli
