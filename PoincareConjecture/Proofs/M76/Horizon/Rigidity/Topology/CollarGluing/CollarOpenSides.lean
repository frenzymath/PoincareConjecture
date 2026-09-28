import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.OpenFrontierCollapse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SupportedCollarCollapse



set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {E X : Type*} [TopologicalSpace E] [Zero E]
  [TopologicalSpace X] [T2Space X]




theorem nonempty_openFrontierCollapse_of_bicollar
    {R : Set X} (hR : IsClosed R) {B : Set E} (hB : IsCompact B)
    (HB : B ≃ₜ frontier R) (c : E × ℝ → X)
    (hc : ContinuousOn c (B ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding
      (fun z : (B ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    (hbase : ∀ x : B, c ((x : E), 0) = HB x)
    (hmarks : ∀ z : (B ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)),
      (c z ∈ frontier R ↔ (z : E × ℝ).2 = 0) ∧
      (c z ∈ R ↔ 0 ≤ (z : E × ℝ).2) ∧
      (c z ∈ (interior R)ᶜ ↔ (z : E × ℝ).2 ≤ 0))
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ delta →
      IsOpen (c '' (B ×ˢ Ioo (-eps) eps))) :
    Nonempty (OpenFrontierCollapse R) := by
  let r := delta / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hwidth : 2 * r < delta := by dsimp [r]; linarith
  have hsub : B ×ˢ Icc (-delta) delta ⊆ B ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hz, ht⟩
    exact ⟨hz, (neg_le_neg hdeltaOne).trans ht.1, ht.2.trans hdeltaOne⟩
  obtain ⟨D, hzero, hvalue, hfixed, hbaseFixed, hends, hinner⟩ :=
    CollarCollapse.exists_supported_source_family hB hr hwidth c (hc.mono hsub)
      (hi.comp (Topology.IsEmbedding.inclusion hsub)) (hopen delta hdelta le_rfl)
  let W := c '' (B ×ˢ Ioo (-r) r)
  have hWo : IsOpen W := hopen r hr (by linarith)
  have hBW : frontier R ⊆ W := by
    intro x hx
    let z := HB.symm ⟨x, hx⟩
    refine ⟨((z : E), 0), ⟨z.property, by constructor <;> linarith⟩, ?_⟩
    exact (hbase z).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩))
  have hRsub : R ⊆ interior R ∪ W := by
    intro x hx
    by_cases hi : x ∈ interior R
    · exact Or.inl hi
    · exact Or.inr (hBW ⟨hR.closure_eq.symm ▸ hx, hi⟩)
  have hTsub : (interior R)ᶜ ⊆ Rᶜ ∪ W := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact Or.inr (hBW ⟨hR.closure_eq.symm ▸ hxR, hx⟩)
    · exact Or.inl hxR
  have hpos : interior R ∪ W = R ∪ W := by
    apply Subset.antisymm
    · exact union_subset_union interior_subset subset_rfl
    · exact union_subset hRsub subset_union_right
  have hneg : Rᶜ ∪ W = (interior R)ᶜ ∪ W := by
    apply Subset.antisymm
    · exact union_subset_union (compl_subset_compl.mpr interior_subset) subset_rfl
    · exact union_subset hTsub subset_union_right
  have hmoveW (t : unitInterval) : MapsTo (fun x => D (t, x)) W W := by
    rintro y ⟨z, hz, rfl⟩
    have hzdelta : z ∈ B ×ˢ Icc (-delta) delta :=
      ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    change D (t, c z) ∈ W
    rw [hvalue t z hzdelta]
    refine ⟨(z.1, CollarCollapse.move r t z.2), ⟨hz.1, ?_⟩, rfl⟩
    exact abs_lt.mp ((CollarCollapse.abs_move_le hr.le t.property z.2).trans_lt
      (abs_lt.mpr hz.2))
  have hmoveSide (T : Set X)
      (hsign : ∀ (t : unitInterval) z, z ∈ B ×ˢ Icc (-1 : ℝ) 1 →
        c z ∈ T → c (z.1, CollarCollapse.move r t z.2) ∈ T)
      (t : unitInterval) : MapsTo (fun x => D (t, x)) T T := by
    intro y hy
    by_cases hyc : y ∈ c '' (B ×ˢ Ioo (-(2 * r)) (2 * r))
    · obtain ⟨z, hz, rfl⟩ := hyc
      have hzdelta : z ∈ B ×ˢ Icc (-delta) delta :=
        ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
      change D (t, c z) ∈ T
      rw [hvalue t z hzdelta]
      exact hsign t z (hsub hzdelta) hy
    · simpa only [hfixed t y hyc] using hy
  have hpositive (t : unitInterval) : MapsTo (fun x => D (t, x)) R R := by
    apply hmoveSide R
    intro s z hz hzR
    have hm := CollarCollapse.move_mem_Icc hr.le s.property hz.2
    apply ((hmarks ⟨(z.1, CollarCollapse.move r s z.2), hz.1, hm⟩).2.1).mpr
    exact (CollarCollapse.move_nonneg_bounds hr.le s.property
      (((hmarks ⟨z, hz⟩).2.1).mp hzR)).1
  have hnegative (t : unitInterval) :
      MapsTo (fun x => D (t, x)) (interior R)ᶜ (interior R)ᶜ := by
    apply hmoveSide (interior R)ᶜ
    intro s z hz hzR
    have hm := CollarCollapse.move_mem_Icc hr.le s.property hz.2
    apply ((hmarks ⟨(z.1, CollarCollapse.move r s z.2), hz.1, hm⟩).2.2).mpr
    exact (CollarCollapse.move_nonpos_bounds hr.le s.property
      (((hmarks ⟨z, hz⟩).2.2).mp hzR)).1
  refine ⟨{
    overlap := W
    positive := interior R ∪ W
    negative := Rᶜ ∪ W
    overlap_open := hWo
    positive_open := isOpen_interior.union hWo
    negative_open := hR.isOpen_compl.union hWo
    positive_eq := hpos
    negative_eq := hneg
    inter_eq := ?_
    cover := ?_
    frontier_subset := hBW
    motion := D
    motion_zero := hzero
    motion_overlap := hmoveW
    motion_positive := hpositive
    motion_negative := hnegative
    endpoint_overlap := ?_ }⟩
  · ext x
    constructor
    · rintro ⟨hi | hW, hc | hW'⟩
      · exact False.elim (hc (interior_subset hi))
      · exact hW'
      · exact hW
      · exact hW
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ R
    · exact Or.inl (hRsub hx)
    · exact Or.inr (Or.inl hx)
  · rintro y ⟨z, hz, rfl⟩
    change D (1, c z) ∈ frontier R
    rw [hinner z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩]
    exact (hbase ⟨z.1, hz.1⟩) ▸ (HB ⟨z.1, hz.1⟩).property

end PoincareConjecture.M76
