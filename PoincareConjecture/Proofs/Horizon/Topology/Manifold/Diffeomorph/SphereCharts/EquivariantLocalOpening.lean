import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Puncture.LocalOpening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts
import Mathlib.Topology.OpenPartialHomeomorph.Constructions









noncomputable section
set_option autoImplicit false

open Set TopologicalSpace Classical
open scoped Manifold ContDiff Topology

namespace Poincare

open PoincareConjecture

local notation "S3" => UnitThreeSphere



theorem exists_equivariant_diffeomorph_of_local_opening
    (O : Opens S3) (a : S3) (ha : a ∈ O)
    {B K : Set S3} (hB : IsCompact B) (hBO : B ⊆ O)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hdis : Disjoint (O : Set S3) (Neg.neg '' (O : Set S3)))
    (e : OpenPartialHomeomorph S3 S3)
    (hes : e.source = (O : Set S3) \ {a})
    (het : e.target = (O : Set S3) \ B)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x)
    (hifix : ∀ x ∈ e.target, x ∉ K → e.symm x = x) :
    ∃ U V : Opens S3,
      (U : Set S3) = {a, -a}ᶜ ∧ (V : Set S3) = (B ∪ Neg.neg '' B)ᶜ ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) U V ∞,
        (∀ x : U, (D x : S3) =
          if (x : S3) ∈ O then e x else if -(x : S3) ∈ O then -e (-x) else x) ∧
        (∀ y : V, (D.symm y : S3) =
          if (y : S3) ∈ O then e.symm y else if -(y : S3) ∈ O then -e.symm (-y) else y) ∧
        (∀ x y : U, (y : S3) = -(x : S3) → (D y : S3) = -(D x : S3)) ∧
        ∀ x : U, (x : S3) ∉ K ∪ Neg.neg '' K → (D x : S3) = x := by
  have hnmem (T : Set S3) (x : S3) : x ∈ Neg.neg '' T ↔ -x ∈ T := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [neg_neg] using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have hsep (x : S3) (hx : x ∈ O) : -x ∉ O := by
    intro hn
    exact disjoint_left.mp hdis hx ((hnmem _ _).mpr hn)
  have hpair (T : Set S3) (hTO : T ⊆ O) :
      ((O : Set S3) \ T) ∪ Neg.neg '' ((O : Set S3) \ T) =
        (T ∪ Neg.neg '' T)ᶜ ∩ ((O : Set S3) ∪ Neg.neg '' (O : Set S3)) := by
    ext x
    simp only [mem_union, mem_sdiff, hnmem, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro (⟨hxO, hxT⟩ | ⟨hnO, hnT⟩)
      · exact ⟨fun h => h.elim hxT (fun hn => hsep x hxO (hTO hn)), Or.inl hxO⟩
      · refine ⟨fun h => h.elim (fun hx => ?_) hnT, Or.inr hnO⟩
        exact hsep x (hTO hx) hnO
    · rintro ⟨hxT, hxO | hnO⟩
      · exact Or.inl ⟨hxO, fun hx => hxT (Or.inl hx)⟩
      · exact Or.inr ⟨hnO, fun hx => hxT (Or.inr hx)⟩
  let U : Opens S3 := ⟨{a, -a}ᶜ, (isClosed_singleton.union isClosed_singleton).isOpen_compl⟩
  let V : Opens S3 := ⟨(B ∪ Neg.neg '' B)ᶜ,
    (hB.isClosed.union (hB.image continuous_neg).isClosed).isOpen_compl⟩
  let W : Opens S3 := ⟨(O : Set S3) ∪ Neg.neg '' (O : Set S3),
    O.isOpen.union ((Homeomorph.neg S3).isOpenMap _ O.isOpen)⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let J : Diffeomorph (𝓡 3) (𝓡 3) S3 S3 ∞ := {
    toEquiv := Equiv.neg S3
    contMDiff_toFun := contMDiff_neg_sphere
    contMDiff_invFun := contMDiff_neg_sphere }
  let n := (J.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
    J.toHomeomorph.toOpenPartialHomeomorph
  have hns : n.source = Neg.neg '' e.source := by
    ext x
    simp [n, J]
    rfl
  have hnt : n.target = Neg.neg '' e.target := by
    ext x
    simp [n, J]
    rfl
  have hn (x : S3) : n x = -e (-x) := rfl
  have hni (x : S3) : n.symm x = -e.symm (-x) := rfl
  have hne : ContMDiffOn (𝓡 3) (𝓡 3) ∞ n n.source :=
    J.contMDiff.comp_contMDiffOn (he.comp J.contMDiff.contMDiffOn (fun _ hx => hx.1.2))
  have hnei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ n.symm n.target :=
    J.symm.contMDiff.comp_contMDiffOn (hei.comp J.symm.contMDiff.contMDiffOn
      (fun _ hx => hx.2.1))
  have hds : Disjoint e.source n.source := by
    rw [hns]
    exact hdis.mono (hes ▸ sdiff_subset) (image_mono (hes ▸ sdiff_subset))
  have hdt : Disjoint e.target n.target := by
    rw [hnt]
    exact hdis.mono (het ▸ sdiff_subset) (image_mono (het ▸ sdiff_subset))
  let p := e.disjointUnion n hds hdt
  have hps : p.source = e.source ∪ n.source := rfl
  have hpt : p.target = e.target ∪ n.target := rfl
  have hpq (x : S3) : p x = if x ∈ e.source then e x else n x := rfl
  have hpiq (x : S3) : p.symm x = if x ∈ e.target then e.symm x else n.symm x := rfl
  have hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p p.source := by
    rw [hps]
    apply ContMDiffOn.union_of_isOpen _ _ e.open_source n.open_source
    · exact he.congr (fun x hx => by rw [hpq, if_pos hx])
    · exact hne.congr (fun x hx => by rw [hpq, if_neg (fun h => disjoint_left.mp hds h hx)])
  have hpi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p.symm p.target := by
    rw [hpt]
    apply ContMDiffOn.union_of_isOpen _ _ e.open_target n.open_target
    · exact hei.congr (fun x hx => by rw [hpiq, if_pos hx])
    · exact hnei.congr (fun x hx => by rw [hpiq, if_neg (fun h => disjoint_left.mp hdt h hx)])
  have hsource : p.source = (U : Set S3) ∩ W := by
    rw [hps, hns, hes, hpair {a} (singleton_subset_iff.mpr ha)]
    simp only [image_singleton]
    rfl
  have htarget : p.target = (V : Set S3) ∩ W := by
    rw [hpt, hnt, het, hpair B hBO]
    rfl
  have hsupport : K ∪ Neg.neg '' K ⊆ W :=
    union_subset_union hKO (image_mono hKO)
  have hout (x : S3) (hx : x ∉ W) : x ∈ U ↔ x ∈ V := by
    have hxO : x ∉ O := fun h => hx (Or.inl h)
    have hnxO : -x ∉ O := fun h => hx (Or.inr ((hnmem _ _).mpr h))
    have hxa : x ≠ a := fun h => hxO (h.symm ▸ ha)
    have hxna : x ≠ -a := by intro h; apply hnxO; simpa only [h, neg_neg] using ha
    have hxB : x ∉ B := fun h => hxO (hBO h)
    have hnxB : -x ∉ B := fun h => hnxO (hBO h)
    change (x ∉ {a, -a}) ↔ x ∉ B ∪ Neg.neg '' B
    simp only [mem_insert_iff, mem_singleton_iff, hxa, hxna, false_or, not_false_eq_true,
      mem_union, hnmem, hxB, hnxB]
  have hpfix (x : S3) (hx : x ∈ p.source) (hxK : x ∉ K ∪ Neg.neg '' K) : p x = x := by
    by_cases hxe : x ∈ e.source
    · rw [hpq, if_pos hxe]
      exact hfix x hxe (fun h => hxK (Or.inl h))
    · have hxn : -x ∈ e.source := (hnmem _ _).mp (hns ▸ (hps ▸ hx).resolve_left hxe)
      rw [hpq, if_neg hxe, hn, hfix (-x) hxn
        (fun h => hxK (Or.inr ((hnmem _ _).mpr h))), neg_neg]
  have hpifix (x : S3) (hx : x ∈ p.target) (hxK : x ∉ K ∪ Neg.neg '' K) : p.symm x = x := by
    by_cases hxe : x ∈ e.target
    · rw [hpiq, if_pos hxe]
      exact hifix x hxe (fun h => hxK (Or.inl h))
    · have hxn : -x ∈ e.target := (hnmem _ _).mp (hnt ▸ (hpt ▸ hx).resolve_left hxe)
      rw [hpiq, if_neg hxe, hni, hifix (-x) hxn
        (fun h => hxK (Or.inr ((hnmem _ _).mpr h))), neg_neg]
  obtain ⟨D, hD, hDi, hDfix⟩ := exists_diffeomorph_of_local_opening U V W p hsource htarget hp hpi
    (hK.union (hK.image continuous_neg)) hsupport hout hpfix hpifix
  have hDformula (x : U) : (D x : S3) =
      if (x : S3) ∈ O then e x else if -(x : S3) ∈ O then -e (-x) else x := by
    rw [hD]
    by_cases hxO : (x : S3) ∈ O
    · have hxe : (x : S3) ∈ e.source := by
        rw [hes]
        exact ⟨hxO, fun h => x.property (Or.inl h)⟩
      rw [if_pos (show (x : S3) ∈ W from Or.inl hxO), hpq, if_pos hxe, if_pos hxO]
    · rw [if_neg hxO]
      by_cases hnxO : -(x : S3) ∈ O
      · rw [if_pos hnxO, if_pos (show (x : S3) ∈ W from Or.inr ((hnmem _ _).mpr hnxO)),
          hpq, if_neg (fun h => hxO (hes.subset h).1), hn]
      · rw [if_neg hnxO, if_neg (show (x : S3) ∉ W from
          fun h => h.elim hxO (fun hn => hnxO ((hnmem _ _).mp hn)))]
  have hDiformula (x : V) : (D.symm x : S3) =
      if (x : S3) ∈ O then e.symm x else if -(x : S3) ∈ O then -e.symm (-x) else x := by
    rw [hDi]
    by_cases hxO : (x : S3) ∈ O
    · have hxe : (x : S3) ∈ e.target := by
        rw [het]
        exact ⟨hxO, fun h => x.property (Or.inl h)⟩
      rw [if_pos (show (x : S3) ∈ W from Or.inl hxO), hpiq, if_pos hxe, if_pos hxO]
    · rw [if_neg hxO]
      by_cases hnxO : -(x : S3) ∈ O
      · rw [if_pos hnxO, if_pos (show (x : S3) ∈ W from Or.inr ((hnmem _ _).mpr hnxO)),
          hpiq, if_neg (fun h => hxO (het.subset h).1), hni]
      · rw [if_neg hnxO, if_neg (show (x : S3) ∉ W from
          fun h => h.elim hxO (fun hn => hnxO ((hnmem _ _).mp hn)))]
  refine ⟨U, V, rfl, rfl, D, hDformula, hDiformula, ?_, hDfix⟩
  intro x y hy
  rw [hDformula, hDformula, hy, neg_neg]
  by_cases hxO : (x : S3) ∈ O
  · simp only [if_pos hxO, if_neg (hsep _ hxO)]
  · by_cases hnxO : -(x : S3) ∈ O
    · simp only [if_neg hxO, if_pos hnxO, neg_neg]
    · simp only [if_neg hxO, if_neg hnxO]

end Poincare
