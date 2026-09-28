import PoincareConjecture.Proofs.M76.Brown.SpindleHeight
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing











set_option autoImplicit false

open Set

namespace BrownCollar

variable {B : Type*} [MetricSpace B]


def spindle (height : B → ℝ) : Set (B × Ico (0 : ℝ) 1) :=
  {z | (z.2 : ℝ) < height z.1}

theorem isOpen_spindle (height : B → ℝ) (hc : Continuous height) :
    IsOpen (spindle height) :=
  isOpen_lt (continuous_subtype_val.comp continuous_snd) (hc.comp continuous_fst)

theorem isClosed_spindleUpper (height : B → ℝ) (hc : Continuous height) :
    IsClosed (spindleUpper height) :=
  isClosed_le ((hc.comp continuous_fst).div_const 2)
    (continuous_subtype_val.comp continuous_snd)

private theorem spindleUpperHomeomorph_mem_iff (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (N : Set (B × Ico (0 : ℝ) 1)) (hAN : spindle height ⊆ N)
    (z : spindleUpper height) :
    spindleUpperHomeomorph height hc hbounds z ∈ N ↔ z.val ∈ N := by
  by_cases hz : z.val ∈ spindle height
  · apply iff_of_true _ (hAN hz)
    apply hAN
    exact (collapseHeight_le z.val.2.property.1).trans_lt hz
  · rw [spindleUpperHomeomorph_apply_above height hc hbounds z (le_of_not_gt hz)]




noncomputable def spindleRestriction (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (N : Set (B × Ico (0 : ℝ) 1)) (hAN : spindle height ⊆ N) :
    ↥(N ∩ spindleUpper height) ≃ₜ N := by
  let P := spindleUpperHomeomorph height hc hbounds
  have hm := spindleUpperHomeomorph_mem_iff height hc hbounds N hAN
  refine
    { toFun := fun z => ⟨P ⟨z, z.property.2⟩, (hm _).mpr z.property.1⟩
      invFun := fun z => ⟨(P.symm z).val,
        (hm _).mp (by
          change P (P.symm z.val) ∈ N
          rw [P.apply_symm_apply]
          exact z.property), (P.symm z).property⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    change (P.symm (P ⟨z.val, z.property.2⟩)).val = z.val
    exact congrArg (fun w : spindleUpper height => w.val)
      (P.symm_apply_apply ⟨z.val, z.property.2⟩)
  · intro z
    apply Subtype.ext
    change P (P.symm z.val) = z.val
    exact P.apply_symm_apply z.val
  · apply Continuous.subtype_mk
    exact P.continuous.comp (continuous_subtype_val.subtype_mk _)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (P.symm.continuous.comp continuous_subtype_val)

theorem spindleRestriction_apply (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (N : Set (B × Ico (0 : ℝ) 1)) (hAN : spindle height ⊆ N)
    (z : ↥(N ∩ spindleUpper height)) :
    (spindleRestriction height hc hbounds N hAN z : B × Ico (0 : ℝ) 1) =
      spindleUpperHomeomorph height hc hbounds ⟨z, z.property.2⟩ := rfl

theorem spindleRestriction_symm_apply (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (N : Set (B × Ico (0 : ℝ) 1)) (hAN : spindle height ⊆ N) (z : N) :
    ((spindleRestriction height hc hbounds N hAN).symm z : B × Ico (0 : ℝ) 1) =
      ((spindleUpperHomeomorph height hc hbounds).symm z).val := rfl






theorem exists_compact_spindle_conjugation
    (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    {U : Set B} (hpos : ∀ b, 0 < height b ↔ b ∈ U)
    {N M : Set (B × Ico (0 : ℝ) 1)} (hN : IsCompact N) (f : N ≃ₜ M)
    (hAN : closure (spindle height) ⊆ N) (hAM : closure (spindle height) ⊆ M)
    (hbase : ∀ z : N, z.val.1 ∈ closure U → (z.val.2 : ℝ) = 0 →
      (f z : B × Ico (0 : ℝ) 1) = z) :
    ∃ g : N ≃ₜ M,
      (∀ z : N, z.val ∈ closure (spindle (fun b => height b / 2)) →
        (g z : B × Ico (0 : ℝ) 1) = z) ∧
      ∀ z : N, z.val ∉ spindle height → (f z : B × Ico (0 : ℝ) 1) ∉ spindle height →
        g z = f z := by
  let A := spindle height
  let V := spindle (fun b => height b / 2)
  let L := closure V
  let C := spindleUpper height
  have hVA : V ⊆ A := by
    intro z hz
    change (z.2 : ℝ) < height z.1 / 2 at hz
    change (z.2 : ℝ) < height z.1
    have hp := (hbounds z.1).1
    linarith
  have hLN : L ⊆ N := (closure_mono hVA).trans hAN
  have hLM : L ⊆ M := (closure_mono hVA).trans hAM
  have hC : IsClosed C := isClosed_spindleUpper height hc
  have hLproj : L ⊆ (Prod.fst : B × Ico (0 : ℝ) 1 → B) ⁻¹' closure U := by
    apply closure_minimal _ (isClosed_closure.preimage continuous_fst)
    intro z hz
    apply subset_closure ((hpos z.1).mp ?_)
    have hp : 0 < height z.1 / 2 := z.2.property.1.trans_lt hz
    linarith
  have hLheight : L ⊆ {z : B × Ico (0 : ℝ) 1 | (z.2 : ℝ) ≤ height z.1 / 2} :=
    closure_minimal (by
      intro z hz
      change (z.2 : ℝ) ≤ height z.1 / 2
      exact hz.le)
      (isClosed_le (continuous_subtype_val.comp continuous_snd)
        ((hc.comp continuous_fst).div_const 2))
  let P := spindleUpperHomeomorph height hc hbounds
  let PN := spindleRestriction height hc hbounds N (subset_closure.trans hAN)
  let PM := spindleRestriction height hc hbounds M (subset_closure.trans hAM)
  let G : ↥(N ∩ C) ≃ₜ ↥(M ∩ C) := (PN.trans f).trans PM.symm
  have hPbase (z : B × Ico (0 : ℝ) 1) (hzL : z ∈ L) (hzC : z ∈ C) :
      P ⟨z, hzC⟩ = collarBase z.1 := by
    have ht : (z.2 : ℝ) = height z.1 / 2 := le_antisymm (hLheight hzL) hzC
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change collapseHeight (height z.1) z.2 = 0
      rw [ht]
      exact collapseHeight_half (hbounds z.1).1
  have hGfix (z : ↥(N ∩ C)) (hzL : z.val ∈ L) :
      (G z : B × Ico (0 : ℝ) 1) = z := by
    let w : ↥(M ∩ C) := ⟨z, hLM hzL, z.property.2⟩
    have hzN : (PN z : B × Ico (0 : ℝ) 1) = collarBase z.val.1 :=
      hPbase z hzL z.property.2
    have hzM : (PM w : B × Ico (0 : ℝ) 1) = collarBase z.val.1 :=
      hPbase z hzL z.property.2
    have hgw : G z = w := by
      apply PM.injective
      change PM (PM.symm (f (PN z))) = PM w
      rw [PM.apply_symm_apply]
      apply Subtype.ext
      calc
        (f (PN z) : B × Ico (0 : ℝ) 1) = PN z := hbase (PN z)
          (by
            rw [hzN]
            change z.val.1 ∈ closure U
            exact hLproj (a := z.val) hzL)
          (by simp only [hzN, collarBase])
        _ = PM w := hzN.trans hzM.symm
    exact congrArg Subtype.val hgw
  have hoverlap (z : ↥(N ∩ C)) : z.val ∈ L ↔ (G z : B × Ico (0 : ℝ) 1) ∈ L := by
    constructor
    · intro hz
      rwa [hGfix z hz]
    · intro hz
      let w : ↥(N ∩ C) := ⟨G z, hLN hz, (G z).property.2⟩
      have hgw : G w = G z := Subtype.ext (hGfix w hz)
      exact congrArg Subtype.val (G.injective hgw) ▸ hz
  obtain ⟨H, hHG, hHL⟩ := Homeomorph.exists_union_of_compact
    (hN.inter_right hC) (hN.of_isClosed_subset isClosed_closure hLN)
    G (Homeomorph.refl L) hoverlap (fun z hz hzL => hGfix ⟨z, hz⟩ hzL)
  have hNu : (N ∩ C) ∪ L = N := by
    apply Subset.antisymm (union_subset inter_subset_left hLN)
    intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl ⟨hz, hzC⟩
    · apply Or.inr
      apply subset_closure
      change (z.2 : ℝ) < height z.1 / 2
      exact lt_of_not_ge hzC
  have hMu : (M ∩ C) ∪ L = M := by
    apply Subset.antisymm (union_subset inter_subset_left hLM)
    intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl ⟨hz, hzC⟩
    · apply Or.inr
      apply subset_closure
      change (z.2 : ℝ) < height z.1 / 2
      exact lt_of_not_ge hzC
  let g : N ≃ₜ M := (Homeomorph.setCongr hNu.symm).trans
    (H.trans (Homeomorph.setCongr hMu))
  refine ⟨g, ?_, ?_⟩
  · intro z hzL
    change (H ⟨z, _⟩ : B × Ico (0 : ℝ) 1) = z
    exact hHL ⟨z, hzL⟩
  · intro z hzA hfzA
    have hzC : z.val ∈ C := by
      change height z.val.1 / 2 ≤ (z.val.2 : ℝ)
      have hp := (hbounds z.val.1).1
      have hza : height z.val.1 ≤ (z.val.2 : ℝ) := le_of_not_gt hzA
      linarith
    let w : ↥(N ∩ C) := ⟨z, z.property, hzC⟩
    have hPN : PN w = z := by
      apply Subtype.ext
      exact spindleUpperHomeomorph_apply_above height hc hbounds
        ⟨z, hzC⟩ (le_of_not_gt hzA)
    apply Subtype.ext
    change (H ⟨z, _⟩ : B × Ico (0 : ℝ) 1) = f z
    rw [hHG w]
    change (PM.symm (f (PN w)) : B × Ico (0 : ℝ) 1) = f z
    rw [hPN]
    exact spindleUpperHomeomorph_symm_apply_above height hc hbounds
      (f z) (le_of_not_gt hfzA)





theorem exists_compact_spindle_conjugation_fixed_frontier
    (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    {U : Set B} (hpos : ∀ b, 0 < height b ↔ b ∈ U)
    {N M : Set (B × Ico (0 : ℝ) 1)} (hN : IsCompact N) (f : N ≃ₜ M)
    (hAN : closure (spindle height) ⊆ N) (hAM : closure (spindle height) ⊆ M)
    (hbase : ∀ z : N, z.val.1 ∈ closure U → (z.val.2 : ℝ) = 0 →
      (f z : B × Ico (0 : ℝ) 1) = z)
    (hAint : spindle height ⊆ interior N)
    (hAimage : spindle height ⊆ (fun z : N => (f z : B × Ico (0 : ℝ) 1)) ''
      ((Subtype.val : N → B × Ico (0 : ℝ) 1) ⁻¹' interior N)) :
    ∃ g : N ≃ₜ M,
      (∀ z : N, z.val ∈ closure (spindle (fun b => height b / 2)) →
        (g z : B × Ico (0 : ℝ) 1) = z) ∧
      ∀ z : N, z.val ∈ frontier N → g z = f z := by
  obtain ⟨g, hgfix, hgoutside⟩ := exists_compact_spindle_conjugation
    height hc hbounds hpos hN f hAN hAM hbase
  refine ⟨g, hgfix, ?_⟩
  intro z hz
  have hzint : z.val ∉ interior N := (mem_frontier_iff_notMem_interior z.property).mp hz
  apply hgoutside z (fun hzA => hzint (hAint hzA))
  intro hfzA
  obtain ⟨w, hw, hfw⟩ := hAimage hfzA
  have hwz : w = z := f.injective (Subtype.ext hfw)
  exact hzint (hwz ▸ hw)

end BrownCollar
