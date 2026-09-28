import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing

set_option autoImplicit false

open Set

namespace Set

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem IsFinitePLBallPair.exists_extension_of_disjoint_end_intervals
    {s : Set X} {t : Set Y} (d : Bool → Set X) (D : Bool → Set Y)
    (a c : Bool → X) (A C : Bool → Y)
    (hs : IsFinitePLBallPair ℝ s {a false, a true})
    (ht : IsFinitePLBallPair ℝ t {A false, A true})
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, c i})
    (hD : ∀ i, IsFinitePLBallPair ℝ (D i) {A i, C i})
    (hds : ∀ i, d i ⊆ s) (hDt : ∀ i, D i ⊆ t)
    (ha : a false ≠ a true) (hA : A false ≠ A true)
    (hac : ∀ i, a i ≠ c i) (hAC : ∀ i, A i ≠ C i)
    (hdis : Disjoint (d false) (d true)) (hDis : Disjoint (D false) (D true))
    (e : ∀ i, d i ≃ₜ D i) (he : ∀ i, (e i).IsFinitePL)
    (hea : ∀ i, (e i ⟨a i, (hd i).1 (Or.inl rfl)⟩ : Y) = A i)
    (hec : ∀ i, (e i ⟨c i, (hd i).1 (Or.inr rfl)⟩ : Y) = C i) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ i (x : d i), H ⟨x, hds i x.property⟩ = ⟨e i x, hDt i (e i x).property⟩) ∧
      (∀ i (x : s), (x : X) ∈ d i ↔ (H x : Y) ∈ D i) ∧
      ∀ i, (H ⟨a i, hds i ((hd i).1 (Or.inl rfl))⟩ : Y) = A i := by
  have hdtrue : IsFinitePLBallPair ℝ (d true) {c true, a true} := by
    simpa only [pair_comm] using hd true
  have hDtrue : IsFinitePLBallPair ℝ (D true) {C true, A true} := by
    simpa only [pair_comm] using hD true
  obtain ⟨m, hm, _, hunion, hm₀, hm₁⟩ :=
    hs.exists_middle_between_disjoint_ends (hd false) hdtrue (hds false) (hds true)
      ha (hac false) (hac true).symm hdis
  obtain ⟨M, hM, _, hUnion, hM₀, hM₁⟩ :=
    ht.exists_middle_between_disjoint_ends (hD false) hDtrue (hDt false) (hDt true)
      hA (hAC false) (hAC true).symm hDis
  have hoverlap (x : d false) : (x : X) ∈ d true ↔ (e false x : Y) ∈ D true :=
    iff_of_false (fun hx => disjoint_left.mp hdis x.property hx)
      (fun hx => disjoint_left.mp hDis (e false x).property hx)
  have hagree (x : X) (hx₀ : x ∈ d false) (hx₁ : x ∈ d true) :
      (e false ⟨x, hx₀⟩ : Y) = e true ⟨x, hx₁⟩ :=
    (disjoint_left.mp hdis hx₀ hx₁).elim
  obtain ⟨E, hE, hE₀, hE₁⟩ :=
    Homeomorph.exists_union_finitePL (e false) (e true) (he false) (he true) hoverlap hagree
  have hcends (i : Bool) : c i ∈ d false ∪ d true := by
    cases i with
    | false => exact Or.inl ((hd false).1 (Or.inr rfl))
    | true => exact Or.inr ((hd true).1 (Or.inr rfl))
  have hEc (i : Bool) : (E ⟨c i, hcends i⟩ : Y) = C i := by
    cases i with
    | false => exact (hE₀ ⟨c false, (hd false).1 (Or.inr rfl)⟩).trans (hec false)
    | true => exact (hE₁ ⟨c true, (hd true).1 (Or.inr rfl)⟩).trans (hec true)
  have hEciff (i : Bool) (x : (d false ∪ d true : Set X)) :
      (E x : Y) = C i ↔ (x : X) = c i := by
    constructor
    · intro hx
      exact congrArg Subtype.val (E.injective (Subtype.ext (hx.trans (hEc i).symm)))
    · intro hx
      have hxeq : x = ⟨c i, hcends i⟩ := Subtype.ext hx
      simpa only [hxeq] using hEc i
  have hinter : m ∩ (d false ∪ d true) = {c false, c true} := by
    rw [inter_union_distrib_left, hm₀, hm₁, singleton_union]
  have hInter : M ∩ (D false ∪ D true) = {C false, C true} := by
    rw [inter_union_distrib_left, hM₀, hM₁, singleton_union]
  have hmem (x : (d false ∪ d true : Set X)) :
      (x : X) ∈ ({c false, c true} : Set X) ↔ (E x : Y) ∈ ({C false, C true} : Set Y) := by
    simp only [mem_insert_iff, mem_singleton_iff, hEciff]
  obtain ⟨H₀, hH₀, hkeepE, _, _⟩ :=
    hm.exists_union_homeomorph_of_boundary_piece hM hinter hInter E hE hmem
  let H : s ≃ₜ t := (Homeomorph.setCongr hunion.symm).trans
    (H₀.trans (Homeomorph.setCongr hUnion))
  have hH : H.IsFinitePL := hH₀.setCongr hunion hUnion
  have hkeep (i : Bool) (x : d i) : H ⟨x, hds i x.property⟩ =
      ⟨e i x, hDt i (e i x).property⟩ := by
    apply Subtype.ext
    cases i with
    | false =>
        exact (congrArg (fun y : (M ∪ (D false ∪ D true) : Set Y) => (y : Y))
          (hkeepE ⟨x, Or.inl x.property⟩)).trans (hE₀ x)
    | true =>
        exact (congrArg (fun y : (M ∪ (D false ∪ D true) : Set Y) => (y : Y))
          (hkeepE ⟨x, Or.inr x.property⟩)).trans (hE₁ x)
  exact ⟨H, hH, hkeep,
    fun i => H.mem_subset_iff_of_extension (e i) (hds i) (hDt i) (hkeep i),
    fun i => (congrArg (fun y : t => (y : Y))
      (hkeep i ⟨a i, (hd i).1 (Or.inl rfl)⟩)).trans (hea i)⟩

end Set
