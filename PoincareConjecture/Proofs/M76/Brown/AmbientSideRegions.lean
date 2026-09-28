import PoincareConjecture.Proofs.M76.Brown.FiniteAmbientAgreement
import PoincareConjecture.Proofs.M76.Brown.OrientedFlatteningCharts

set_option autoImplicit false

open Set SignType

namespace BrownCollar

variable {X P : Type*} [MetricSpace X] [TopologicalSpace P]

theorem exists_ambient_side_regions {S : Set X} (hS : IsCompact S)
    (E : S → OpenPartialHomeomorph X (P × ℝ))
    (hcover : ∀ x : S, (x : X) ∈ (E x).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hgerm : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V) :
    ∃ W Rpos Rneg : Set X, IsOpen W ∧ S ⊆ W ∧
      Rpos ∪ Rneg = W ∧ Rpos ∩ Rneg = S ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rpos) ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rneg) ∧
      ∀ x : S, ∃ (i : S) (V : Set X), IsOpen V ∧ (x : X) ∈ V ∧
        V ⊆ (E i).source ∧ V ⊆ W ∧
        ∀ y ∈ V, (y ∈ Rpos ↔ 0 ≤ (E i y).2) ∧
          (y ∈ Rneg ↔ (E i y).2 ≤ 0) := by
  classical
  obtain ⟨U, t, hU, ht⟩ := exists_finite_shrunken_cover hS
    (fun i : S => (E i).source) (fun i => (E i).open_source) id hcover
  let O' : t → Set X := fun i => (E i.val).source
  let U' : t → Set X := fun i => U i.val
  let g : t → X → SignType := fun i y => sign (E i.val y).2
  obtain ⟨N, hN, hSN, hEq⟩ := exists_open_ambient_agreement S O' U' g
    (fun i => (hU i.val).2.2) (fun i j x hx hxO => hgerm i.val j.val ⟨x, hx⟩ hxO)
  let W := N ∩ ⋃ i : t, U' i
  have hW : IsOpen W := hN.inter (isOpen_iUnion (fun i : t => (hU i.val).1))
  have hSW : S ⊆ W := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨hSN hx, mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩⟩
  have hUO (i : t) : U' i ⊆ (E i.val).source :=
    subset_closure.trans (hU i.val).2.2
  let Pos := ⋃ i : t, W ∩ (U' i ∩ {y | 0 < (E i.val y).2})
  let Neg := ⋃ i : t, W ∩ (U' i ∩ {y | (E i.val y).2 < 0})
  have hPos : IsOpen Pos := isOpen_iUnion (fun i : t =>
    hW.inter (((E i.val).continuousOn.mono (hUO i)).snd.isOpen_inter_preimage
      (hU i.val).1 isOpen_Ioi))
  have hNeg : IsOpen Neg := isOpen_iUnion (fun i : t =>
    hW.inter (((E i.val).continuousOn.mono (hUO i)).snd.isOpen_inter_preimage
      (hU i.val).1 isOpen_Iio))
  have hpos (i : t) (y : X) (hyW : y ∈ W) (hyi : y ∈ U' i) :
      y ∈ Pos ↔ 0 < (E i.val y).2 := by
    constructor
    · intro hy
      obtain ⟨j, _, hyj, hjpos⟩ := mem_iUnion.mp hy
      have heq : sign (E i.val y).2 = sign (E j.val y).2 :=
        hEq i j ⟨⟨hyW.1, hyi⟩, hyj⟩
      exact sign_eq_one_iff.mp (heq.trans (sign_pos hjpos))
    · intro hy
      exact mem_iUnion.mpr ⟨i, hyW, hyi, hy⟩
  have hneg (i : t) (y : X) (hyW : y ∈ W) (hyi : y ∈ U' i) :
      y ∈ Neg ↔ (E i.val y).2 < 0 := by
    constructor
    · intro hy
      obtain ⟨j, _, hyj, hjneg⟩ := mem_iUnion.mp hy
      have heq : sign (E i.val y).2 = sign (E j.val y).2 :=
        hEq i j ⟨⟨hyW.1, hyi⟩, hyj⟩
      exact sign_eq_neg_one_iff.mp (heq.trans (sign_neg hjneg))
    · intro hy
      exact mem_iUnion.mpr ⟨i, hyW, hyi, hy⟩
  let Rpos := W \ Neg
  let Rneg := W \ Pos
  have hRp (i : t) (y : X) (hyW : y ∈ W) (hyi : y ∈ U' i) :
      y ∈ Rpos ↔ 0 ≤ (E i.val y).2 := by
    change (y ∈ W ∧ y ∉ Neg) ↔ _
    rw [and_iff_right hyW, hneg i y hyW hyi, not_lt]
  have hRm (i : t) (y : X) (hyW : y ∈ W) (hyi : y ∈ U' i) :
      y ∈ Rneg ↔ (E i.val y).2 ≤ 0 := by
    change (y ∈ W ∧ y ∉ Pos) ↔ _
    rw [and_iff_right hyW, hpos i y hyW hyi, not_lt]
  have hunion : Rpos ∪ Rneg = W := by
    apply Subset.antisymm
    · exact union_subset (fun _ h => h.1) (fun _ h => h.1)
    · intro y hy
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy.2
      rcases le_total 0 (E i.val y).2 with hp | hm
      · exact Or.inl ((hRp i y hy hyi).mpr hp)
      · exact Or.inr ((hRm i y hy hyi).mpr hm)
  have hinter : Rpos ∩ Rneg = S := by
    ext y
    constructor
    · intro hy
      have hyW : y ∈ W := hy.1.1
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyW.2
      exact (hpair i.val y (hUO i hyi)).mpr
        (le_antisymm ((hRm i y hyW hyi).mp hy.2) ((hRp i y hyW hyi).mp hy.1))
    · intro hyS
      have hyW := hSW hyS
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyW.2
      have hz := (hpair i.val y (hUO i hyi)).mp hyS
      exact ⟨(hRp i y hyW hyi).mpr hz.symm.le, (hRm i y hyW hyi).mpr hz.le⟩
  have hRpclosed : IsClosed ((Subtype.val : W → X) ⁻¹' Rpos) := by
    have heq : (Subtype.val : W → X) ⁻¹' Rpos =
        ((Subtype.val : W → X) ⁻¹' Neg)ᶜ := by
      ext y
      exact and_iff_right y.property
    rw [heq]
    exact (hNeg.preimage continuous_subtype_val).isClosed_compl
  have hRmclosed : IsClosed ((Subtype.val : W → X) ⁻¹' Rneg) := by
    have heq : (Subtype.val : W → X) ⁻¹' Rneg =
        ((Subtype.val : W → X) ⁻¹' Pos)ᶜ := by
      ext y
      exact and_iff_right y.property
    rw [heq]
    exact (hPos.preimage continuous_subtype_val).isClosed_compl
  refine ⟨W, Rpos, Rneg, hW, hSW, hunion, hinter, hRpclosed, hRmclosed, ?_⟩
  intro x
  have hxW := hSW x.property
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxW.2
  refine ⟨i.val, W ∩ U' i, hW.inter (hU i.val).1, ⟨hxW, hxi⟩,
    inter_subset_right.trans (hUO i), inter_subset_left, ?_⟩
  intro y hy
  exact ⟨hRp i y hy.1 hy.2, hRm i y hy.1 hy.2⟩

end BrownCollar
