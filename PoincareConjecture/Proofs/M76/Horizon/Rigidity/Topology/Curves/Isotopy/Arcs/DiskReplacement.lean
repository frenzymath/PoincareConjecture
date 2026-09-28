import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

private theorem exists_disk_extension_fix_rim_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D T U W Z : Set E} {a b : E}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W))
    (hT : IsFinitePLBallPair (ℝ × ℝ) T (U ∪ Z))
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hUW : U ∩ W = {a, b}) (hUZ : U ∩ Z = {a, b})
    (q : W ≃ₜ Z) (hq : q.IsFinitePL)
    (hends : ∀ x : W, (x : E) ∈ ({a, b} : Set E) → (q x : E) = x) :
    ∃ H : D ≃ₜ T, H.IsFinitePL ∧
      (∀ x : U, (H ⟨x, hD.1 (Or.inl x.property)⟩ : E) = x) ∧
      (∀ x : W, (H ⟨x, hD.1 (Or.inr x.property)⟩ : E) = q x) := by
  have hUcopy := hU
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKU, _⟩, _⟩, _⟩ := hUcopy
  have hid : (Homeomorph.refl U).IsFinitePL :=
    ⟨id, ⟨K, hK, hKU, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,
      fun _ => rfl⟩
  have hoverlap (x : U) : (x : E) ∈ W ↔ ((Homeomorph.refl U) x : E) ∈ Z := by
    constructor
    · intro hx
      exact (hUZ.symm.subset (hUW.subset ⟨x.property, hx⟩)).2
    · intro hx
      exact (hUW.symm.subset (hUZ.subset ⟨x.property, hx⟩)).2
  obtain ⟨F, hF, hFU, hFW⟩ := Homeomorph.exists_union_finitePL
    (Homeomorph.refl U) q hid hq hoverlap (fun x hxU hxW =>
      (hends ⟨x, hxW⟩ (hUW.subset ⟨hxU, hxW⟩)).symm)
  obtain ⟨H, hH, hHF, _⟩ := hD.exists_extension hT F hF
  refine ⟨H, hH, ?_, ?_⟩
  · intro x
    exact (congrArg (fun y : T => (y : E)) (hHF ⟨x, Or.inl x.property⟩)).trans (hFU x)
  · intro x
    exact (congrArg (fun y : T => (y : E)) (hHF ⟨x, Or.inr x.property⟩)).trans (hFW x)

theorem exists_finitePL_proper_arc_replacement_fix_rim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q W Z : Set E} {a b : E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hZ : IsFinitePLBallPair ℝ Z {a, b})
    (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b)
    (hproperW : W \ {a, b} ⊆ S \ Q)
    (hproperZ : Z \ {a, b} ⊆ S \ Q)
    (q : W ≃ₜ Z) (hq : q.IsFinitePL)
    (hends : ∀ x : W, (x : E) ∈ ({a, b} : Set E) → (q x : E) = x) :
    ∃ H : S ≃ₜ S, H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ x : S, (x : E) ∈ Q → H x = x) ∧
      (∀ (x : W) (hx : (x : E) ∈ S), (H ⟨x, hx⟩ : E) = q x) ∧
      ∀ x : S, (x : E) ∈ W ↔ (H x : E) ∈ Z := by
  obtain ⟨U, V, hU, hV, hUV, hUVi⟩ := hS.exists_boundary_arcs ha hb hab
  have hcutIntersection {L A : Set E} (hL : IsFinitePLBallPair ℝ L {a, b})
      (hA : IsFinitePLBallPair ℝ A {a, b}) (hAQ : A ⊆ Q)
      (hproper : L \ {a, b} ⊆ S \ Q) : A ∩ L = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper ⟨hx.2, hn⟩).2 (hAQ hx.1)
    · exact fun x hx => ⟨hA.1 hx, hL.1 hx⟩
  have hUQ : U ⊆ Q := subset_union_left.trans hUV.subset
  have hVQ : V ⊆ Q := subset_union_right.trans hUV.subset
  obtain ⟨D₀, D₁, hD₀, hD₁, hDunion, hDinter, _, _⟩ :=
    hS.exists_proper_arc_cut hU hV hW hab hUVi.subset hUV hproperW
  obtain ⟨T₀, T₁, hT₀, hT₁, hTunion, hTinter, _, _⟩ :=
    hS.exists_proper_arc_cut hU hV hZ hab hUVi.subset hUV hproperZ
  obtain ⟨H₀, hH₀, hH₀U, hH₀W⟩ := exists_disk_extension_fix_rim_piece hD₀ hT₀ hU
    (hcutIntersection hW hU hUQ hproperW) (hcutIntersection hZ hU hUQ hproperZ)
    q hq hends
  have hD₁' : IsFinitePLBallPair (ℝ × ℝ) D₁ (V ∪ W) := by
    simpa only [union_comm] using hD₁
  have hT₁' : IsFinitePLBallPair (ℝ × ℝ) T₁ (V ∪ Z) := by
    simpa only [union_comm] using hT₁
  obtain ⟨H₁, hH₁, hH₁V, hH₁W⟩ := exists_disk_extension_fix_rim_piece hD₁' hT₁' hV
    (hcutIntersection hW hV hVQ hproperW) (hcutIntersection hZ hV hVQ hproperZ)
    q hq hends
  have hW₀ : W ⊆ D₀ := subset_union_right.trans hD₀.1
  have hZ₀ : Z ⊆ T₀ := subset_union_right.trans hT₀.1
  have hkeep₀ (x : W) : H₀ ⟨x, hW₀ x.property⟩ = ⟨q x, hZ₀ (q x).property⟩ :=
    Subtype.ext (hH₀W x)
  have hoverlap (x : D₀) : (x : E) ∈ D₁ ↔ (H₀ x : E) ∈ T₁ := by
    have hw := H₀.mem_subset_iff_of_extension q hW₀ hZ₀ hkeep₀ x
    constructor
    · intro hx
      exact (hTinter.symm.subset (hw.mp (hDinter.subset ⟨x.property, hx⟩))).2
    · intro hx
      exact (hDinter.symm.subset (hw.mpr (hTinter.subset ⟨(H₀ x).property, hx⟩))).2
  obtain ⟨G, hG, hG₀, hG₁⟩ := Homeomorph.exists_union_finitePL H₀ H₁ hH₀ hH₁
    hoverlap (by
      intro x hx₀ hx₁
      have hxW := hDinter.subset ⟨hx₀, hx₁⟩
      exact (hH₀W ⟨x, hxW⟩).trans (hH₁W ⟨x, hxW⟩).symm)
  let H : S ≃ₜ S := (Homeomorph.setCongr hDunion.symm).trans
    (G.trans (Homeomorph.setCongr hTunion))
  have hH : H.IsFinitePL := hG.setCongr hDunion hTunion
  have hkeep (x : W) (hx : (x : E) ∈ S) : (H ⟨x, hx⟩ : E) = q x :=
    (hG₀ ⟨x, hW₀ x.property⟩).trans (hH₀W x)
  have hWS : W ⊆ S := hW₀.trans (subset_union_left.trans hDunion.subset)
  have hZS : Z ⊆ S := hZ₀.trans (subset_union_left.trans hTunion.subset)
  refine ⟨H, hH, hH.symm, ?_, hkeep, ?_⟩
  · intro x hx
    apply Subtype.ext
    rcases hUV.symm.subset hx with hxU | hxV
    · exact (hG₀ ⟨x, hD₀.1 (Or.inl hxU)⟩).trans (hH₀U ⟨x, hxU⟩)
    · exact (hG₁ ⟨x, hD₁'.1 (Or.inl hxV)⟩).trans (hH₁V ⟨x, hxV⟩)
  · exact H.mem_subset_iff_of_extension q hWS hZS (fun x => Subtype.ext (hkeep x _))

end PoincareConjecture.M76.Dehn
