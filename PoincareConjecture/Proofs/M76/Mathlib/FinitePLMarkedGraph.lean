import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem IsFinitePLBallPair.exists_marked_interval_homeomorph
    {s : Set E} {t : Set F} {a b : E} {c d : F}
    (hs : IsFinitePLBallPair ℝ s {a, b})
    (ht : IsFinitePLBallPair ℝ t {c, d}) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : s ≃ₜ t, e.IsFinitePL ∧
      (∀ x : s, (e x : F) = c ↔ (x : E) = a) ∧
      (∀ x : s, (e x : F) = d ↔ (x : E) = b) := by
  obtain ⟨es, hes, hesa, hesb⟩ := hs.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨et, het, hetc, hetd⟩ := ht.exists_unitInterval_chart_with_endpoints hcd
  let e := es.symm.trans et
  have ha : a ∈ s := hs.1 (by simp)
  have hb : b ∈ s := hs.1 (by simp)
  have hea : (e ⟨a, ha⟩ : F) = c := by
    have h : (⟨a, ha⟩ : s) = es ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := Subtype.ext hesa.symm
    rw [h]
    change (et (es.symm (es _)) : F) = c
    rw [es.symm_apply_apply]
    exact hetc
  have heb : (e ⟨b, hb⟩ : F) = d := by
    have h : (⟨b, hb⟩ : s) = es ⟨1, ⟨zero_le_one, le_rfl⟩⟩ := Subtype.ext hesb.symm
    rw [h]
    change (et (es.symm (es _)) : F) = d
    rw [es.symm_apply_apply]
    exact hetd
  refine ⟨e, hes.symm.trans het, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact congrArg Subtype.val (e.injective (Subtype.ext (hx.trans hea.symm)))
    · intro hx
      have h : x = ⟨a, ha⟩ := Subtype.ext hx
      simpa only [h] using hea
  · intro x
    constructor
    · intro hx
      exact congrArg Subtype.val (e.injective (Subtype.ext (hx.trans heb.symm)))
    · intro hx
      have h : x = ⟨b, hb⟩ := Subtype.ext hx
      simpa only [h] using heb






theorem exists_finitePL_marked_graph {ι : Type*} [Finite ι]
    (S : ι → Set E) (T : ι → Set F) {a b : E} {c d : F}
    (hS : ∀ i, IsFinitePLBallPair ℝ (S i) {a, b})
    (hT : ∀ i, IsFinitePLBallPair ℝ (T i) {c, d})
    (hab : a ≠ b) (hcd : c ≠ d)
    (hSinter : Pairwise (fun i j => S i ∩ S j = {a, b}))
    (hTinter : Pairwise (fun i j => T i ∩ T j = {c, d})) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      (∀ x : ⋃ i, S i, (H x : F) = c ↔ (x : E) = a) ∧
      (∀ x : ⋃ i, S i, (H x : F) = d ↔ (x : E) = b) := by
  classical
  choose e he hea heb using fun i =>
    (hS i).exists_marked_interval_homeomorph (hT i) hab hcd
  have hoverlap (i j : ι) (x : S i) : (x : E) ∈ S j ↔ (e i x : F) ∈ T j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true x.property (e i x).property
    have hx : (x : E) ∈ S j ↔ (x : E) ∈ ({a, b} : Set E) := by
      rw [← hSinter hij]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (e i x : F) ∈ ({c, d} : Set F) ↔ (e i x : F) ∈ T j := by
      rw [← hTinter hij]
      simp only [mem_inter_iff, (e i x).property, true_and]
    have hmarks : (x : E) ∈ ({a, b} : Set E) ↔ (e i x : F) ∈ ({c, d} : Set F) := by
      simp only [mem_insert_iff, mem_singleton_iff, hea i x, heb i x]
    exact hx.trans (hmarks.trans hy)
  have hagree (i j : ι) (x : E) (hi : x ∈ S i) (hj : x ∈ S j) :
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩ := by
    by_cases hij : i = j
    · subst j
      rfl
    have hx : x ∈ ({a, b} : Set E) := (hSinter hij).subset ⟨hi, hj⟩
    rcases hx with hx | hx
    · exact ((hea i ⟨x, hi⟩).mpr hx).trans ((hea j ⟨x, hj⟩).mpr hx).symm
    · exact ((heb i ⟨x, hi⟩).mpr hx).trans ((heb j ⟨x, hj⟩).mpr hx).symm
  obtain ⟨H, hH, hkeep⟩ := Homeomorph.exists_iUnion_finitePL S T e he hoverlap hagree
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro i x
    exact H.mem_subset_iff_of_extension (e i)
      (fun y hy => mem_iUnion.mpr ⟨i, hy⟩)
      (fun y hy => mem_iUnion.mpr ⟨i, hy⟩)
      (fun y => Subtype.ext (hkeep i y)) x
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    have hx : (H x : F) = e i ⟨x, hi⟩ := hkeep i ⟨x, hi⟩
    rw [hx]
    exact hea i ⟨x, hi⟩
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    have hx : (H x : F) = e i ⟨x, hi⟩ := hkeep i ⟨x, hi⟩
    rw [hx]
    exact heb i ⟨x, hi⟩

end Set
