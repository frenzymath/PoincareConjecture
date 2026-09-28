import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card







noncomputable section
set_option autoImplicit false

open Set
open scoped BigOperators

namespace Poincare.Topology



theorem card_preimage_eq_two_of_range_inter_eq_pair
    {I X : Type*} {b : I → X} (hb : Function.Injective b) {C : Set X}
    {p q : X} (hpq : p ≠ q) (hinter : range b ∩ C = {p, q}) :
    Nat.card {i : I // b i ∈ C} = 2 := by
  change Nat.card (b ⁻¹' C) = 2
  rw [← Nat.card_image_of_injective hb, image_preimage_eq_inter_range, inter_comm,
    hinter]
  exact Set.ncard_pair hpq


theorem card_eq_two_of_card_four_of_card_fiber_two
    {I J : Type*} [Finite I] (f : I → J) (hf : Function.Surjective f)
    (hI : Nat.card I = 4) (hfiber : ∀ j, Nat.card {i // f i = j} = 2) :
    Nat.card J = 2 := by
  classical
  let : Finite J := Finite.of_surjective f hf
  let : Fintype J := Fintype.ofFinite J
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma, hI] at h
  simp only [hfiber, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    (show Nat.card J * 2 = 2 * 2 by simpa [Nat.card_eq_fintype_card] using h)



theorem connectedComponents_eq_iff_mem
    {X : Type*} [TopologicalSpace X] {K : Set X} (p q : K) :
    ConnectedComponents.mk p = ConnectedComponents.mk q ↔
      (p : X) ∈ connectedComponentIn K q := by
  rw [ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image q.property]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨r, hr, heq⟩
    have : r = p := Subtype.ext heq
    exact this ▸ hr



theorem card_connectedComponents_eq_two_of_boundary_fibers
    {X I : Type*} [TopologicalSpace X] [Finite I] {K : Set X}
    (b : I → K) (hI : Nat.card I = 4)
    (hfiber : ∀ q : K,
      Nat.card {i : I // (b i : X) ∈ connectedComponentIn K q} = 2) :
    Nat.card (ConnectedComponents K) = 2 := by
  let f : I → ConnectedComponents K := fun i => ConnectedComponents.mk (b i)
  have hcard (q : K) : Nat.card {i // f i = ConnectedComponents.mk q} = 2 := by
    have heq : {i : I | f i = ConnectedComponents.mk q} =
        {i : I | (b i : X) ∈ connectedComponentIn K q} := by
      ext i
      exact connectedComponents_eq_iff_mem (b i) q
    change Nat.card {i : I | f i = ConnectedComponents.mk q} = 2
    rw [heq]
    exact hfiber q
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
    have hn : Nonempty {i // f i = ConnectedComponents.mk q} :=
      (Nat.card_ne_zero.mp (by rw [hcard]; decide)).1
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, hi⟩
  apply card_eq_two_of_card_four_of_card_fiber_two f hsurj hI
  intro c
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
  exact hcard q


theorem nonempty_connectedComponents_equiv_fin_two_of_boundary_fibers
    {X I : Type*} [TopologicalSpace X] [Finite I] {K : Set X}
    (b : I → K) (hI : Nat.card I = 4)
    (hfiber : ∀ q : K,
      Nat.card {i : I // (b i : X) ∈ connectedComponentIn K q} = 2) :
    Nonempty (ConnectedComponents K ≃ Fin 2) := by
  have hc := card_connectedComponents_eq_two_of_boundary_fibers b hI hfiber
  have hn : Nat.card (ConnectedComponents K) ≠ 0 := by rw [hc]; decide
  exact ⟨(Nat.equivFinOfCardPos hn).trans (finCongr hc)⟩

end Poincare.Topology
