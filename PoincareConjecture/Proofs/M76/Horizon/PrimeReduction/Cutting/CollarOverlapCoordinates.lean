import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedCollarOpenCoordinates
import Mathlib.Topology.Homeomorph.Lemmas









set_option autoImplicit false

noncomputable section

open Set Topology

namespace PoincareConjecture.M76.CollarOverlap

def endInterval (b : Bool) : Set ℝ :=
  Ioo (if b then 3 / 4 else 0) (if b then 1 else 1 / 4)

def endParameter (b : Bool) (t : endInterval b) : unitInterval :=
  ⟨t, by
    have ht := t.property
    cases b <;> dsimp [endInterval] at ht
    all_goals constructor <;> linarith [ht.1, ht.2]⟩

theorem endParameter_embedding (b : Bool) : IsEmbedding (endParameter b) :=
  (IsEmbedding.subtypeVal.of_comp_iff).mp IsEmbedding.subtypeVal

theorem endParameter_range (b : Bool) (t : endInterval b) :
    (0 : ℝ) < endParameter b t ∧ (endParameter b t : ℝ) < 1 ∧
      ((endParameter b t : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < endParameter b t) := by
  have ht := t.property
  cases b <;> dsimp [endParameter, endInterval] at ht ⊢
  · exact ⟨ht.1, by linarith [ht.2], Or.inl ht.2⟩
  · exact ⟨by linarith [ht.1], ht.2, Or.inr ht.1⟩

variable {X κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
  {A : κ → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
  {C : κ → Set X}

def halfCollar (W : ∀ i, (A i × unitInterval) ≃ₜ C i) (k : κ × Bool) : Set X :=
  (fun z => (W k.1 z : X)) ''
    {z | if k.2 then (1 / 2 : ℝ) ≤ z.2 else (z.2 : ℝ) ≤ 1 / 2}

omit [Finite κ] in
theorem halfCollar_closed (W : ∀ i, (A i × unitInterval) ≃ₜ C i) (k : κ × Bool) :
    IsClosed (halfCollar W k) := by
  have hc : IsClosed {z : A k.1 × unitInterval |
      if k.2 then (1 / 2 : ℝ) ≤ z.2 else (z.2 : ℝ) ≤ 1 / 2} := by
    cases k.2
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · exact isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  exact (hc.isCompact.image (continuous_subtype_val.comp (W k.1).continuous)).isClosed

omit [Finite κ] [T2Space X] [∀ i, CompactSpace (A i)] in
theorem end_mem_halfCollar_iff
    (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (i : κ) (b : Bool) (a : A i) (t : endInterval b) (k : κ × Bool) :
    (W i (a, endParameter b t) : X) ∈ halfCollar W k ↔ (i, b) = k := by
  constructor
  · rintro ⟨z, hz, he⟩
    have hik : i = k.1 := by
      by_contra hn
      exact disjoint_left.mp (hdis hn) (W i (a, endParameter b t)).property
        (he ▸ (W k.1 z).property)
    rcases k with ⟨j, c⟩
    dsimp at hik
    subst j
    have hez := (W i).injective (Subtype.ext he)
    subst z
    have hbc : b = c := by
      have ht := t.property
      cases b <;> cases c <;> try rfl
      all_goals dsimp [endParameter, endInterval] at ht hz
      all_goals exfalso; linarith [ht.1, ht.2]
    exact Prod.ext rfl hbc
  · rintro rfl
    refine ⟨(a, endParameter b t), ?_, rfl⟩
    have ht := t.property
    cases b <;> dsimp [endParameter, endInterval] at ht ⊢ <;>
      linarith [ht.1, ht.2]

theorem exists_overlap_homeomorph
    (R : Set X) (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hCR : ∀ i, C i ⊆ R) (hOC : ∀ i, O i ⊆ C i)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    ∃ H : (Σ k : κ × Bool, A k.1 × endInterval k.2) ≃ₜ
        ↥(collarCoverOuter R W ∩ collarCoverInner R O),
      ∀ k z, ((H ⟨k, z⟩).val : X) = W k.1 (z.1, endParameter k.2 z.2) := by
  let T := collarCoverOuter R W ∩ collarCoverInner R O
  let f : (Σ k : κ × Bool, A k.1 × endInterval k.2) → T := fun z =>
    ⟨⟨W z.1.1 (z.2.1, endParameter z.1.2 z.2.2), hCR _ (W _ _).property⟩,
      (collarCoverOuter_coordinates R W hCR hdis _ _).mpr
        (endParameter_range _ _).2.2,
      mem_iUnion.mpr ⟨z.1.1, (hO _ _).mpr
        ⟨(endParameter_range _ _).1, (endParameter_range _ _).2.1⟩⟩⟩
  have hfval (z) : ((f z).val : X) = W z.1.1 (z.2.1, endParameter z.1.2 z.2.2) := rfl
  have hfemb (k : κ × Bool) : IsEmbedding (f ∘ Sigma.mk k) := by
    have he := IsEmbedding.subtypeVal.comp ((W k.1).isEmbedding.comp
      (IsEmbedding.id.prodMap (endParameter_embedding k.2)))
    exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).of_comp_iff.mp he
  have hfind : IsInducing f := by
    apply inducing_sigma.mpr
    refine ⟨fun k => (hfemb k).isInducing, ?_⟩
    intro k
    let U : Set T := (fun x : T => (x.val : X)) ⁻¹'
      (⋃ j : {j : κ × Bool // j ≠ k}, halfCollar W j.val)ᶜ
    refine ⟨U, ?_, ?_⟩
    · exact (isClosed_iUnion_of_finite
        (fun j : {j : κ × Bool // j ≠ k} => halfCollar_closed W j.val)).isOpen_compl.preimage
        (continuous_subtype_val.comp continuous_subtype_val)
    · intro z
      change (¬ ((f z).val : X) ∈ ⋃ j : {j : κ × Bool // j ≠ k}, halfCollar W j.val) ↔ _
      rw [hfval]
      simp only [mem_iUnion, end_mem_halfCollar_iff W hdis]
      constructor
      · intro hz
        by_contra hn
        exact hz ⟨⟨z.1, hn⟩, rfl⟩
      · intro hz ⟨j, hj⟩
        exact j.property (hj.symm.trans hz)
  have hfinj : Function.Injective f := by
    intro z w he
    have hval := congrArg (fun x : T => (x.val : X)) he
    have hk : z.1 = w.1 := by
      apply (end_mem_halfCollar_iff W hdis z.1.1 z.1.2 z.2.1 z.2.2 w.1).mp
      rw [← hfval, hval, hfval]
      exact (end_mem_halfCollar_iff W hdis w.1.1 w.1.2 w.2.1 w.2.2 w.1).mpr rfl
    cases z with | mk k z =>
      cases w with | mk l w =>
        dsimp at hk
        subst l
        exact congrArg (Sigma.mk k) ((hfemb k).injective he)
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.2
    let z := (W i).symm ⟨x, hOC i hi⟩
    have hz : (W i z : X) = x := congrArg Subtype.val ((W i).apply_symm_apply _)
    have hoz := (hO i z).mp (hz ▸ hi)
    have hou : (z.2 : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < z.2 := by
      apply (collarCoverOuter_coordinates R W hCR hdis i z).mp
      have he : (⟨W i z, hCR i (W i z).property⟩ : R) = x := Subtype.ext hz
      rw [he]
      exact hx.1
    rcases hou with hlo | hhi
    · let t : endInterval false := ⟨z.2, hoz.1, hlo⟩
      refine ⟨⟨(i, false), z.1, t⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    · let t : endInterval true := ⟨z.2, hhi, hoz.2⟩
      refine ⟨⟨(i, true), z.1, t⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hz
  exact ⟨({ toIsInducing := hfind, injective := hfinj } : IsEmbedding f).toHomeomorphOfSurjective
    hfsurj, fun _ _ => rfl⟩

end PoincareConjecture.M76.CollarOverlap
