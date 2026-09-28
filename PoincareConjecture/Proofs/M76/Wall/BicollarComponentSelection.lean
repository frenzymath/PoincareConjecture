import PoincareConjecture.Proofs.M76.Wall.BicollarBaseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.LocalComplementarySides

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {A C K : Set X}

theorem exists_bicollar_exterior_component
    (H : (A × Ioo (-1 : ℝ) 1) ≃ₜ C) (hC : IsOpen C)
    (hbase : ∀ a, (H (bicollarBase a) : X) = (a : X))
    (hside : ∀ z, (H z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ))
    (hA : IsConnected A) (hAK : A ⊆ K) :
    ∃ q ∈ Kᶜ, A ⊆ frontier (connectedComponentIn Kᶜ q) ∧
      ∀ x ∈ Kᶜ,
        ((frontier (connectedComponentIn Kᶜ x) ∩ A).Nonempty ↔
          connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ q) ∧
        (connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ q →
          ∀ y ∈ C, y ∈ (connectedComponentIn Kᶜ x)ᶜ ↔ y ∈ K) := by
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
  let N := range (negativeBicollarMap H)
  have hN : IsConnected N := isConnected_range_negativeBicollarMap H
  have hNK : N ⊆ Kᶜ := by
    rintro _ ⟨z, rfl⟩ hk
    have ht := (hside
      (z.1, ⟨z.2.val, z.2.property.1, lt_trans z.2.property.2 (by norm_num)⟩)).mp hk
    exact (not_le_of_gt z.2.property.2) ht
  obtain ⟨q, hqN⟩ := hN.nonempty
  let E := connectedComponentIn Kᶜ q
  have hNE : N ⊆ E := hN.isPreconnected.subset_connectedComponentIn hqN hNK
  have hAE : A ⊆ frontier E := by
    intro a ha
    refine ⟨closure_mono hNE (base_subset_closure_negativeBicollarMap H hbase ha), ?_⟩
    intro hai
    exact connectedComponentIn_subset Kᶜ q (interior_subset hai) (hAK ha)
  refine ⟨q, hNK hqN, hAE, ?_⟩
  intro x hx
  let U := connectedComponentIn Kᶜ x
  have hnegative (y : C) (hy : (y : X) ∉ K) : (y : X) ∈ N := by
    let z := H.symm y
    have hHz : (H z : X) = (y : X) := congrArg Subtype.val (H.apply_symm_apply y)
    have ht : (z.2 : ℝ) < 0 := by
      apply lt_of_not_ge
      intro hnonneg
      exact hy (hHz ▸ (hside z).mpr hnonneg)
    have hm := mem_range_negativeBicollarMap H z ht
    exact hHz ▸ hm
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨a, haU, haA⟩
      have haC : a ∈ C := by
        have hm := (H (bicollarBase (⟨a, haA⟩ : A))).property
        simpa only [hbase] using hm
      obtain ⟨y, hyC, hyU⟩ := mem_closure_iff.mp haU.1 C hC haC
      have hyE : y ∈ E := hNE (hnegative ⟨y, hyC⟩
        (connectedComponentIn_subset Kᶜ x hyU))
      exact (connectedComponentIn_eq hyU).trans (connectedComponentIn_eq hyE).symm
    · intro hUE
      obtain ⟨a, ha⟩ := hA.nonempty
      refine ⟨a, ?_, ha⟩
      rw [hUE]
      exact hAE ha
  · intro hUE y hyC
    constructor
    · intro hyU
      by_contra hyK
      have hyE : y ∈ E := hNE (hnegative ⟨y, hyC⟩ hyK)
      have hyU' : y ∈ U := by
        change y ∈ connectedComponentIn Kᶜ x
        rw [hUE]
        exact hyE
      exact hyU hyU'
    · intro hyK hyU
      exact connectedComponentIn_subset Kᶜ x hyU hyK

end BrownCollar
