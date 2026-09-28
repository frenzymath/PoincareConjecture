import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapChartPasting
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  {K D : Set X} {O : Set E} {r : ℝ}

local notation "P" => Set.prod (Ico (0 : ℝ) r) O
local notation "N" => Set.prod (Ioc (-r) (0 : ℝ)) O
local notation "T" => Set.prod (Ioo (-r) r) O

theorem exists_cap_chart_of_relative_half_embeddings
    (hK : IsClosed K) (hD : IsClosed D) (hcover : K ∪ D = univ)
    (hO : IsOpen O) (hne : O.Nonempty) (hr : 0 < r)
    (e : P → K) (he : Topology.IsOpenEmbedding e)
    (f : N → D) (hf : Topology.IsOpenEmbedding f)
    (heD : ∀ p : P, (e p : X) ∈ D ↔ (p : ℝ × E).1 = 0)
    (hfK : ∀ p : N, (f p : X) ∈ K ↔ (p : ℝ × E).1 = 0)
    (hzero : ∀ (p : P) (q : N), (p : ℝ × E) = (q : ℝ × E) →
      (e p : X) = (f q : X)) :
    ∃ H : OpenPartialHomeomorph X (ℝ × E),
      H.source = range (fun p : P => (e p : X)) ∪ range (fun p : N => (f p : X)) ∧
      H.target = T ∧
      (∀ p : P, H (e p : X) = (p : ℝ × E)) ∧
      ∀ p : N, H (f p : X) = (p : ℝ × E) := by
  let es : P → X := fun p => e p
  let fs : N → X := fun p => f p
  let A := range es
  let B := range fs
  let U := A ∪ B
  have hes : Topology.IsEmbedding es := Topology.IsEmbedding.subtypeVal.comp he.isEmbedding
  have hfs : Topology.IsEmbedding fs := Topology.IsEmbedding.subtypeVal.comp hf.isEmbedding
  let a : P ≃ₜ A := hes.toHomeomorph
  let b : N ≃ₜ B := hfs.toHomeomorph
  have haval (p : P) : (a p : X) = (e p : X) := rfl
  have hbval (p : N) : (b p : X) = (f p : X) := rfl
  have hainv (x : A) : (e (a.symm x) : X) = (x : X) :=
    congrArg Subtype.val (a.apply_symm_apply x)
  have hbinv (x : B) : (f (b.symm x) : X) = (x : X) :=
    congrArg Subtype.val (b.apply_symm_apply x)
  have hAK : A ⊆ K := by rintro x ⟨p, rfl⟩; exact (e p).property
  have hBD : B ⊆ D := by rintro x ⟨p, rfl⟩; exact (f p).property
  have hAD : A ∩ D ⊆ B := by
    rintro x ⟨⟨p, rfl⟩, hpD⟩
    have hp0 := (heD p).mp hpD
    let q : N := ⟨p, by
      exact ⟨⟨by simpa only [hp0] using neg_lt_zero.mpr hr, hp0.le⟩, p.property.2⟩⟩
    exact ⟨q, (hzero p q rfl).symm⟩
  have hBK : B ∩ K ⊆ A := by
    rintro x ⟨⟨q, rfl⟩, hqK⟩
    have hq0 := (hfK q).mp hqK
    let p : P := ⟨q, ⟨⟨hq0.ge, by simpa only [hq0] using hr⟩, q.property.2⟩⟩
    exact ⟨p, hzero p q rfl⟩
  have hUK : (Subtype.val : K → X) ⁻¹' U = range e := by
    ext x
    constructor
    · intro hx
      have hxA : (x : X) ∈ A := hx.elim id (fun h => hBK ⟨h, x.property⟩)
      obtain ⟨p, hp⟩ := hxA
      exact ⟨p, Subtype.ext hp⟩
    · rintro ⟨p, rfl⟩
      exact Or.inl ⟨p, rfl⟩
  have hUD : (Subtype.val : D → X) ⁻¹' U = range f := by
    ext x
    constructor
    · intro hx
      have hxB : (x : X) ∈ B := hx.elim (fun h => hAD ⟨h, x.property⟩) id
      obtain ⟨p, hp⟩ := hxB
      exact ⟨p, Subtype.ext hp⟩
    · rintro ⟨p, rfl⟩
      exact Or.inr ⟨p, rfl⟩
  have hU : IsOpen U := by
    apply isClosed_compl_iff.mp
    have hsplit : Uᶜ =
        (Subtype.val : K → X) '' ((Subtype.val : K → X) ⁻¹' Uᶜ) ∪
          (Subtype.val : D → X) '' ((Subtype.val : D → X) ⁻¹' Uᶜ) := by
      rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range,
        Subtype.range_coe, Subtype.range_coe, ← inter_union_distrib_left, hcover, inter_univ]
    rw [hsplit, preimage_compl, preimage_compl, hUK, hUD]
    exact (hK.isClosedEmbedding_subtypeVal.isClosedMap _ he.isOpen_range.isClosed_compl).union
      (hD.isClosedEmbedding_subtypeVal.isClosedMap _ hf.isOpen_range.isClosed_compl)
  have hUA : IsClosed ((Subtype.val : U → X) ⁻¹' A) := by
    have heq : (Subtype.val : U → X) ⁻¹' A = (Subtype.val : U → X) ⁻¹' K := by
      ext x
      exact ⟨fun hx => hAK hx, fun hx => x.property.elim id (fun h => hBK ⟨h, hx⟩)⟩
    rw [heq]
    exact hK.preimage continuous_subtype_val
  have hUB : IsClosed ((Subtype.val : U → X) ⁻¹' B) := by
    have heq : (Subtype.val : U → X) ⁻¹' B = (Subtype.val : U → X) ⁻¹' D := by
      ext x
      exact ⟨fun hx => hBD hx, fun hx => x.property.elim (fun h => hAD ⟨h, hx⟩) id⟩
    rw [heq]
    exact hD.preimage continuous_subtype_val
  have hPN : P ∪ N = T := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩
      · exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
    · intro hz
      by_cases hz0 : 0 ≤ z.1
      · exact Or.inl ⟨⟨hz0, hz.1.2⟩, hz.2⟩
      · exact Or.inr ⟨⟨hz.1.1, (not_le.mp hz0).le⟩, hz.2⟩
  have htP : IsClosed ((Subtype.val : ↥(P ∪ N : Set (ℝ × E)) → ℝ × E) ⁻¹' P) := by
    have heq : (Subtype.val : ↥(P ∪ N : Set (ℝ × E)) → ℝ × E) ⁻¹' P =
        {z : ↥(P ∪ N : Set (ℝ × E)) | 0 ≤ (z : ℝ × E).1} := by
      ext z
      have hz : (z : ℝ × E) ∈ T := hPN ▸ z.property
      exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hz.1.2⟩, hz.2⟩⟩
    rw [heq]
    exact isClosed_le continuous_const (continuous_fst.comp continuous_subtype_val)
  have htN : IsClosed ((Subtype.val : ↥(P ∪ N : Set (ℝ × E)) → ℝ × E) ⁻¹' N) := by
    have heq : (Subtype.val : ↥(P ∪ N : Set (ℝ × E)) → ℝ × E) ⁻¹' N =
        {z : ↥(P ∪ N : Set (ℝ × E)) | (z : ℝ × E).1 ≤ 0} := by
      ext z
      have hz : (z : ℝ × E) ∈ T := hPN ▸ z.property
      exact ⟨fun h => h.1.2, fun h => ⟨⟨hz.1.1, h⟩, hz.2⟩⟩
    rw [heq]
    exact isClosed_le (continuous_fst.comp continuous_subtype_val) continuous_const
  have hoverlap (x : A) : (x : X) ∈ B ↔ (a.symm x : ℝ × E) ∈ N := by
    constructor
    · intro hx
      have hp0 := (heD (a.symm x)).mp (by rw [hainv]; exact hBD hx)
      exact ⟨⟨by simpa only [hp0] using neg_lt_zero.mpr hr, hp0.le⟩,
        (a.symm x).property.2⟩
    · intro hx
      have hp0 : (a.symm x : ℝ × E).1 = 0 :=
        le_antisymm hx.1.2 (a.symm x).property.1.1
      apply hAD
      refine ⟨x.property, ?_⟩
      rw [← hainv]
      exact (heD _).mpr hp0
  have hagree (x : X) (hxA : x ∈ A) (hxB : x ∈ B) :
      (a.symm ⟨x, hxA⟩ : ℝ × E) = (b.symm ⟨x, hxB⟩ : ℝ × E) := by
    let p := a.symm ⟨x, hxA⟩
    let q := b.symm ⟨x, hxB⟩
    have hpN : (p : ℝ × E) ∈ N := (hoverlap ⟨x, hxA⟩).mp hxB
    let q0 : N := ⟨p, hpN⟩
    have hq : f q0 = f q := by
      apply Subtype.ext
      rw [← hzero p q0 rfl]
      exact (hainv ⟨x, hxA⟩).trans (hbinv ⟨x, hxB⟩).symm
    exact congrArg Subtype.val (hf.injective hq)
  obtain ⟨z, hz⟩ := hne
  let p0 : P := ⟨(0, z), ⟨⟨le_rfl, hr⟩, hz⟩⟩
  obtain ⟨H, hHs, hHt, hHa, hHb⟩ := exists_open_cap_chart_of_closed_halves
    hU (hPN.symm ▸ (isOpen_Ioo.prod hO)) ⟨es p0, Or.inl ⟨p0, rfl⟩⟩
    hUA hUB htP htN a.symm b.symm hoverlap hagree
  refine ⟨H, hHs, hHt.trans hPN, ?_, ?_⟩
  · intro p
    have h := hHa (a p)
    rw [a.symm_apply_apply] at h
    exact h
  · intro p
    have h := hHb (b p)
    rw [b.symm_apply_apply] at h
    exact h

end PoincareConjecture.M76
