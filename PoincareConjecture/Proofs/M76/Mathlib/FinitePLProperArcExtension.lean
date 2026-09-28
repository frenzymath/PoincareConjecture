import PoincareConjecture.Proofs.M76.Mathlib.FinitePLAttachedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePLBallPair.exists_extension_of_proper_arc
    {s q w : Set E} {t r W : Set F} {a b : E} {A B : F}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (ht : IsFinitePLBallPair (ℝ × ℝ) t r)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {A, B})
    (hab : a ≠ b) (hAB : A ≠ B)
    (ha : a ∈ q) (hb : b ∈ q) (hA : A ∈ r) (hB : B ∈ r)
    (hproper : w \ {a, b} ⊆ s \ q)
    (hProper : W \ {A, B} ⊆ t \ r)
    (e : w ≃ₜ W) (he : e.IsFinitePL)
    (hends : ∀ x : w, (x : E) ∈ ({a, b} : Set E) ↔
      (e x : F) ∈ ({A, B} : Set F)) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ (x : w) (hx : (x : E) ∈ s), (H ⟨x, hx⟩ : F) = e x) ∧
      (∀ x : s, (x : E) ∈ w ↔ (H x : F) ∈ W) ∧
      ∀ x : s, (x : E) ∈ q ↔ (H x : F) ∈ r := by
  obtain ⟨u, v, hu, hv, huv, huvi⟩ := hs.exists_boundary_arcs ha hb hab
  obtain ⟨U, V, hU, hV, hUV, hUVi⟩ := ht.exists_boundary_arcs hA hB hAB
  have huq : u ⊆ q := subset_union_left.trans huv.subset
  have hUr : U ⊆ r := subset_union_left.trans hUV.subset
  have huw : u ∩ w = ({a, b} : Set E) := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper ⟨hx.2, hn⟩).2 (huq hx.1)
    · exact fun x hx => ⟨hu.1 hx, hw.1 hx⟩
  have hUW : U ∩ W = ({A, B} : Set F) := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hProper ⟨hx.2, hn⟩).2 (hUr hx.1)
    · exact fun x hx => ⟨hU.1 hx, hW.1 hx⟩
  obtain ⟨d, c, hd, _, hdc, _, _, _⟩ :=
    hs.exists_proper_arc_cut hu hv hw hab huvi.subset huv hproper
  obtain ⟨D, C, hD, _, hDC, _, _, _⟩ :=
    ht.exists_proper_arc_cut hU hV hW hAB hUVi.subset hUV hProper
  have hds : d ⊆ s := subset_union_left.trans hdc.subset
  have hDt : D ⊆ t := subset_union_left.trans hDC.subset
  have hwd : w ⊆ d := subset_union_right.trans hd.1
  have hWD : W ⊆ D := subset_union_right.trans hD.1
  obtain ⟨ed, hed, hedw, hedu, hedwm⟩ :=
    hd.exists_extension_of_boundary_piece hD hu hU huw hUW e he hends
  obtain ⟨H, hH, hHd, _, _, hHq⟩ := hs.exists_extension_of_attached_disk ht
    hd hds hD hDt hu huq hw hab hproper hU hUr hW hAB hProper
    ed hed hedu hedwm
  have hkeep (x : w) : H ⟨x, hds (hwd x.property)⟩ =
      ⟨e x, hDt (hWD (e x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : t => (y : F)) (hHd ⟨x, hwd x.property⟩)).trans
      (congrArg (fun y : D => (y : F)) (hedw x))
  refine ⟨H, hH, ?_,
    H.mem_subset_iff_of_extension e (hwd.trans hds) (hWD.trans hDt) hkeep, hHq⟩
  intro x hx
  exact congrArg Subtype.val (hkeep x)

end Set
