import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Basic



noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Analysis.Calculus.Morse



theorem exists_finite_cuts_between {C : Set Real} (hC : C.Finite) :
    ∃ A : Set Real, A.Finite ∧ Disjoint A C ∧
      ∀ a ∈ C, ∀ b ∈ C, a < b -> ∃ t ∈ A, a < t ∧ t < b := by
  classical
  let : Finite C := hC.to_subtype
  let J := {p : C × C // (p.1 : Real) < p.2}
  have hchoice (p : J) : ∃ t : Real,
      t ∈ Ioo (p.val.1 : Real) p.val.2 ∧ t ∉ C :=
    (Ioo_infinite p.property).exists_notMem_finite hC
  choose t ht using hchoice
  refine ⟨range t, finite_range t, ?_, ?_⟩
  · rw [disjoint_left]
    rintro x ⟨p, rfl⟩ hx
    exact (ht p).2 hx
  · intro a ha b hb hab
    let p : J := ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
    exact ⟨t p, ⟨p, rfl⟩, (ht p).1⟩



theorem eq_of_same_connected_component_of_cuts
    {C A : Set Real}
    (hcuts : ∀ a ∈ C, ∀ b ∈ C, a < b -> ∃ t ∈ A, a < t ∧ t < b)
    {a b : Real} (ha : a ∈ C) (hb : b ∈ C)
    (hsame : b ∈ connectedComponentIn Aᶜ a) : a = b := by
  have hconn := isConnected_connectedComponentIn_iff.mpr
    (connectedComponentIn_nonempty_iff.mp ⟨b, hsame⟩)
  have ha' : a ∈ connectedComponentIn Aᶜ a :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp ⟨b, hsame⟩)
  rcases lt_trichotomy a b with hab | rfl | hba
  · obtain ⟨t, ht, hat, htb⟩ := hcuts a ha b hb hab
    have htin := hconn.isPreconnected.ordConnected.out ha' hsame ⟨hat.le, htb.le⟩
    exact False.elim ((connectedComponentIn_subset _ _ htin) ht)
  · rfl
  · obtain ⟨t, ht, hbt, hta⟩ := hcuts b hb a ha hba
    have htin := hconn.isPreconnected.ordConnected.out hsame ha' ⟨hbt.le, hta.le⟩
    exact False.elim ((connectedComponentIn_subset _ _ htin) ht)

end Poincare.Analysis.Calculus.Morse
