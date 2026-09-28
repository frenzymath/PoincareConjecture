import PoincareConjecture.Proofs.M47.SeedPositiveTestHistory
import PoincareConjecture.Proofs.M47.SeedPositiveOnset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem seed_component_birth_le_positive_test
    (hC : RicciFlowCurvatureTheory.{u}) {F : SurgeryFlowData.{u}} {J : Set ℝ}
    (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T s0 b : ℝ} {I : Set ℝ} {V : Set (F.slice T).carrier}
    (hI : Icc s0 0 ⊆ I) (hJ : Icc (T + s0) T ⊆ J)
    (test : SurgeryFlowCylinder F (F.slice T) T 1 I V)
    (testBased : ∀ hs y, y ∈ V → HEq (test.forward 0 hs y) y)
    (x : (F.slice T).carrier) (hx : x ∈ V) (hs0 : s0 ≤ 0)
    (hpositive : SurgeryPositiveComponentAt F (T + s0 / 1)
      (test.forward s0 (hI ⟨le_rfl, hs0⟩) x))
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier)) (hxU : x ∈ U)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U) (hb : b ≤ 0)
    (based : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hbirth : T + b / 1 = 0 ∨ ∃ hbirth : T + b / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (T + b / 1)).carrier],
        ∃ i : Fin (F.event (T + b / 1) hbirth).cap_count,
          (e.forward b ⟨le_rfl, hb⟩ '' (U : Set (F.slice T).carrier) ∩
            ((F.event (T + b / 1) hbirth).caps i).carrier).Nonempty) :
    b ≤ s0 := by
  by_contra hnot
  have hs0b : s0 < b := lt_of_not_ge hnot
  have hs0time : 0 ≤ T + s0 / 1 := F.time_domain_nonnegative
    (test.time_subset (mem_image_of_mem _ (hI ⟨le_rfl, hs0⟩)))
  have hnotzero : T + b / 1 ≠ 0 := by
    simp only [div_one] at hs0time ⊢
    linarith only [hs0time, hs0b]
  obtain ⟨hbirthTime, hcap⟩ := hbirth.resolve_left hnotzero
  have hbtest : b ∈ I := hI ⟨hs0b.le, hb⟩
  have hagree : e.forward b ⟨le_rfl, hb⟩ x = test.forward b hbtest x :=
    PoincareConjecture.M47.seedM15_cylinder_eq_of_terminal e test hb
      (Subset.refl _) ((Icc_subset_Icc hs0b.le le_rfl).trans hI) x hxU x hx
      (eq_of_heq ((based _ x hxU).trans (testBased _ x hx).symm))
  let : Nonempty (F.slice (T + b / 1)).carrier := ⟨e.forward b ⟨le_rfl, hb⟩ x⟩
  obtain ⟨i, hi⟩ := hcap
  have himage := PoincareConjecture.M47.component_cylinder_image_eq e U.isOpen hcompact
    hconnected b ⟨le_rfl, hb⟩ hxU
  rw [himage, hagree] at hi
  have hbJ : T + b / 1 ∈ J := hJ (by
    simp only [div_one]
    exact ⟨by linarith, by linarith⟩)
  exact seed_search_nonpositive_of_cap_endpoint hC hpolicy test hx
    (hI ⟨le_rfl, hs0⟩) hbtest hs0b hbJ hbirthTime hi hpositive

theorem seed_component_onset_le_positive_test
    {F : SurgeryFlowData.{u}} {T s0 a b : ℝ}
    {I : Set ℝ} {V : Set (F.slice T).carrier}
    (hI : Icc s0 0 ⊆ I)
    (test : SurgeryFlowCylinder F (F.slice T) T 1 I V)
    (testBased : ∀ hs y, y ∈ V → HEq (test.forward 0 hs y) y)
    (x : (F.slice T).carrier) (hx : x ∈ V) (hs0 : s0 ≤ 0)
    (hpositive : SurgeryPositiveComponentAt F (T + s0 / 1)
      (test.forward s0 (hI ⟨le_rfl, hs0⟩) x))
    (U : TopologicalSpace.Opens (F.slice T).carrier) (hxU : x ∈ U)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (based : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hb : b ≤ s0)
    (hbefore : ∀ s ∈ Ico b a, ∀ (hs : s ∈ Icc b 0) (y : U),
      ¬ SurgeryPositiveComponentAt F (T + s / 1) (e.forward s hs y.val)) :
    a ≤ s0 := by
  by_contra hnot
  have hs0a : s0 < a := lt_of_not_ge hnot
  have hagree : e.forward s0 ⟨hb, hs0⟩ x =
      test.forward s0 (hI ⟨le_rfl, hs0⟩) x :=
    PoincareConjecture.M47.seedM15_cylinder_eq_of_terminal e test hs0
      (Icc_subset_Icc hb le_rfl) hI x hxU x hx
      (eq_of_heq ((based _ x hxU).trans (testBased _ x hx).symm))
  apply hbefore s0 ⟨hb, hs0a⟩ ⟨hb, hs0⟩ ⟨x, hxU⟩
  rwa [hagree]

end PoincareConjecture.Proofs.M47
