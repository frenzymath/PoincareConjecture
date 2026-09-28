import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCut
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle











set_option autoImplicit false

open Set

namespace Set





theorem capped_zero_section_eq_residual_of_disjoint {X : Type*}
    {s s' b d R Z : Set X} (hsection : (s ∪ s') ∩ Z = b ∪ R)
    (hbd : b ⊆ d) (hdR : Disjoint d R) :
    ((s ∪ d) ∩ Z) \ d = R ∩ s := by
  ext x
  constructor
  · rintro ⟨⟨hxs | hxd, hxZ⟩, hxnd⟩
    · have hxR := (hsection.subset ⟨Or.inl hxs, hxZ⟩).resolve_left
        (fun hxb => hxnd (hbd hxb))
      exact ⟨hxR, hxs⟩
    · exact (hxnd hxd).elim
  · intro hx
    exact ⟨⟨Or.inl hx.2, (hsection.symm.subset (Or.inr hx.1)).2⟩,
      fun hxd => disjoint_left.mp hdR hxd hx.1⟩

end Set

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

omit [Finite ι] in




theorem exists_ordinary_zero_section_cut_partition
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (j : ι) {s₀ s₁ d Z : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcut : s₀ ∩ s₁ = (P j).boundary ℝ) (hbd : (P j).boundary ℝ ⊆ d)
    (hsection : (s₀ ∪ s₁) ∩ Z = ⋃ i, (P i).boundary ℝ)
    (hdP : ∀ i, i ≠ j → Disjoint d ((P i).boundary ℝ)) :
    ∃ I : Set {i : ι // i ≠ j},
      (((s₀ ∪ d) ∩ Z) \ d) = ⋃ i : I, (P i.val.val).boundary ℝ ∧
      (((s₁ ∪ d) ∩ Z) \ d) =
        ⋃ i : (Iᶜ : Set {i : ι // i ≠ j}), (P i.val.val).boundary ℝ := by
  let D (i : {i : ι // i ≠ j}) := (P i.val).boundary ℝ
  have hsection' : (s₀ ∪ s₁) ∩ Z = (P j).boundary ℝ ∪ ⋃ i, D i := by
    rw [hsection]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.val, hi⟩
  have hpre (i : {i : ι // i ≠ j}) : IsPreconnected (D i) := by
    obtain ⟨e⟩ := (P i.val).nonempty_boundary_homeomorph_circle (hPe i.val) (hPi i.val)
    exact (isConnected_iff_connectedSpace.mpr
      (e.connectedSpace_iff.mpr inferInstance)).isPreconnected
  have hcover (i : {i : ι // i ≠ j}) : D i ⊆ s₀ ∪ s₁ := fun x hx =>
    (hsection'.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))).1
  have hinter (i : {i : ι // i ≠ j}) : D i ∩ (s₀ ∩ s₁) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp (hdP i.val i.property) (hbd (hcut.subset hx.2)) hx.1
  obtain ⟨I, _, _, h₀, h₁⟩ := exists_connected_cut_partition hs₀ hs₁ D hpre hcover hinter
  have hdR : Disjoint d (⋃ i, D i) := by
    apply disjoint_left.mpr
    intro x hxd hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hdP i.val i.property) hxd hi
  refine ⟨I, (capped_zero_section_eq_residual_of_disjoint hsection' hbd hdR).trans h₀, ?_⟩
  have hsection'' : (s₁ ∪ s₀) ∩ Z = (P j).boundary ℝ ∪ ⋃ i, D i := by
    rw [union_comm s₁ s₀]
    exact hsection'
  exact (capped_zero_section_eq_residual_of_disjoint hsection'' hbd hdR).trans h₁






theorem exists_decreasing_ordinary_zero_presentations_with_residue_free_charges
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {r : Set E} (hr : r.Subsingleton)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ r))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (j : ι) {s₀ s₁ d Z : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcut : s₀ ∩ s₁ = (P j).boundary ℝ) (hbd : (P j).boundary ℝ ⊆ d)
    (hsection : (s₀ ∪ s₁) ∩ Z = ⋃ i, (P i).boundary ℝ)
    (hdP : ∀ i, i ≠ j → Disjoint d ((P i).boundary ℝ)) :
    ∃ a₀ a₁ : ℕ,
      HasAlexanderCurvePresentation (((s₀ ∪ d) ∩ Z) \ d) a₀ ∧
      HasAlexanderCurvePresentation (((s₁ ∪ d) ∩ Z) \ d) a₁ ∧
      a₀ + a₁ < alexanderCurveCount (fun i => (P i).boundary ℝ) ∧
      (Disjoint r s₀ → a₀ = 0) ∧ (Disjoint r s₁ → a₁ = 0) := by
  obtain ⟨I, h₀, h₁⟩ := exists_ordinary_zero_section_cut_partition n P
    (fun i => (hP i).2) (fun i => (hP i).1) j hs₀ hs₁ hcut hbd hsection hdP
  have hpresent (J : Set {i : ι // i ≠ j}) :
      HasAlexanderCurvePresentation (⋃ i : J, (P i.val.val).boundary ℝ)
        (alexanderCurveCount (fun i : J => (P i.val.val).boundary ℝ)) := by
    let R : Set E := r ∩ ⋃ i : J, (P i.val.val).boundary ℝ
    apply hasAlexanderCurvePresentation_of_family
      (fun i : J => n i.val.val) (fun i => P i.val.val) (fun i => hP i.val.val)
      (r := R) (hr.anti inter_subset_left)
    · exact (union_eq_self_of_subset_left inter_subset_right).symm
    · intro i k hik x hx
      exact ⟨hpair (fun h => hik (Subtype.ext (Subtype.ext h))) hx,
        mem_iUnion.mpr ⟨i, hx.1⟩⟩
  have hdecrease := alexanderCurveCount_partition_after_deletion
    (fun i => (P i).boundary ℝ) hbranch j I
  have hvanish (J : Set {i : ι // i ≠ j}) (s : Set E)
      (hJs : (⋃ i : J, (P i.val.val).boundary ℝ) ⊆ s) (hrs : Disjoint r s) :
      alexanderCurveCount (fun i : J => (P i.val.val).boundary ℝ) = 0 := by
    apply (alexanderCurveCount_eq_zero_iff _).mpr
    intro i k hik
    apply disjoint_left.mpr
    intro x hxi hxk
    exact disjoint_left.mp hrs
      (hpair (fun h => hik (Subtype.ext (Subtype.ext h))) ⟨hxi, hxk⟩)
      (hJs (mem_iUnion.mpr ⟨i, hxi⟩))
  refine ⟨_, _, h₀.symm ▸ hpresent I, h₁.symm ▸ hpresent Iᶜ,
    lt_of_lt_of_le (Nat.lt_succ_self _) hdecrease.1, ?_, ?_⟩
  · intro hrs
    apply hvanish I s₀ _ hrs
    intro x hx
    have hxd := h₀.symm.subset hx
    exact hxd.1.1.resolve_right hxd.2
  · intro hrs
    apply hvanish Iᶜ s₁ _ hrs
    intro x hx
    have hxd := h₁.symm.subset hx
    exact hxd.1.1.resolve_right hxd.2






theorem exists_decreasing_ordinary_zero_presentations
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {r : Set E} (hr : r.Subsingleton)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ r))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (j : ι) {s₀ s₁ d Z : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcut : s₀ ∩ s₁ = (P j).boundary ℝ) (hbd : (P j).boundary ℝ ⊆ d)
    (hsection : (s₀ ∪ s₁) ∩ Z = ⋃ i, (P i).boundary ℝ)
    (hdP : ∀ i, i ≠ j → Disjoint d ((P i).boundary ℝ)) :
    ∃ a₀ a₁ : ℕ,
      HasAlexanderCurvePresentation (((s₀ ∪ d) ∩ Z) \ d) a₀ ∧
      HasAlexanderCurvePresentation (((s₁ ∪ d) ∩ Z) \ d) a₁ ∧
      a₀ + a₁ < alexanderCurveCount (fun i => (P i).boundary ℝ) := by
  obtain ⟨a₀, a₁, hzero₀, hzero₁, hlt, _, _⟩ :=
    exists_decreasing_ordinary_zero_presentations_with_residue_free_charges
      n P hP hr hpair hbranch j hs₀ hs₁ hcut hbd hsection hdP
  exact ⟨a₀, a₁, hzero₀, hzero₁, hlt⟩

end Polygon
