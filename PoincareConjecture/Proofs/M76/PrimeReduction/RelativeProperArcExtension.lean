import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRelativeAttachedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_extension_of_proper_arc_fix_boundary
    {s q w W : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ q) (hb : b ∈ q)
    (hproper : w \ {a, b} ⊆ s \ q)
    (hProper : W \ {a, b} ⊆ s \ q)
    (e : w ≃ₜ W) (he : e.IsFinitePL)
    (hfix : ∀ x : w, (x : E) ∈ ({a, b} : Set E) → (e x : E) = x) :
    ∃ H : s ≃ₜ s, H.IsFinitePL ∧
      (∀ (x : w) (hx : (x : E) ∈ s), (H ⟨x, hx⟩ : E) = e x) ∧
      (∀ x : s, (x : E) ∈ q → H x = x) ∧
      ∀ x : s, (x : E) ∈ w ↔ (H x : E) ∈ W := by
  obtain ⟨u, v, hu, hv, huv, huvi⟩ := hs.exists_boundary_arcs ha hb hab
  have huq : u ⊆ q := subset_union_left.trans huv.subset
  have huw : u ∩ w = ({a, b} : Set E) := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper ⟨hx.2, hn⟩).2 (huq hx.1)
    · exact fun x hx => ⟨hu.1 hx, hw.1 hx⟩
  have huW : u ∩ W = ({a, b} : Set E) := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hProper ⟨hx.2, hn⟩).2 (huq hx.1)
    · exact fun x hx => ⟨hu.1 hx, hW.1 hx⟩
  obtain ⟨d, c, hd, _, hdc, _, _, _⟩ :=
    hs.exists_proper_arc_cut hu hv hw hab huvi.subset huv hproper
  obtain ⟨D, C, hD, _, hDC, _, _, _⟩ :=
    hs.exists_proper_arc_cut hu hv hW hab huvi.subset huv hProper
  have hds : d ⊆ s := subset_union_left.trans hdc.subset
  have hDs : D ⊆ s := subset_union_left.trans hDC.subset
  have hid {t r : Set E} (ht : IsFinitePLBallPair ℝ t r) :
      FinitePiecewiseAffineOn (id : E → E) t := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKt, _⟩, _⟩, _⟩ := ht
    exact ⟨K, hK, hKt, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  have hiu : (Homeomorph.refl u).IsFinitePL := ⟨id, hid hu, fun _ => rfl⟩
  have hiq : (Homeomorph.refl q).IsFinitePL := by
    refine ⟨id, ?_, fun _ => rfl⟩
    rw [← huv]
    exact finitePiecewiseAffineOn_union (hid hu) (hid hv)
  have hoverlap (x : u) : (x : E) ∈ w ↔ (x : E) ∈ W := by
    constructor
    · intro hx
      exact hW.1 (huw.subset ⟨x.property, hx⟩)
    · intro hx
      exact hw.1 (huW.subset ⟨x.property, hx⟩)
  obtain ⟨eb, heb, hebu, hebw⟩ := Homeomorph.exists_union_finitePL
    (Homeomorph.refl u) e hiu he hoverlap
    (fun x hxu hxw => (hfix ⟨x, hxw⟩ (huw.subset ⟨hxu, hxw⟩)).symm)
  obtain ⟨ed, hed, hedB, _⟩ := hd.exists_extension hD eb heb
  have hudu : u ⊆ d := subset_union_left.trans hd.1
  have hudD : u ⊆ D := subset_union_left.trans hD.1
  have hwd : w ⊆ d := subset_union_right.trans hd.1
  have hWD : W ⊆ D := subset_union_right.trans hD.1
  have hedu (x : u) : ed ⟨x, hudu x.property⟩ = ⟨x, hudD x.property⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : D => (y : E)) (hedB ⟨x, Or.inl x.property⟩)).trans
      (hebu x)
  have hedw (x : w) : ed ⟨x, hwd x.property⟩ = ⟨e x, hWD (e x).property⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : D => (y : E)) (hedB ⟨x, Or.inr x.property⟩)).trans
      (hebw x)
  obtain ⟨H, hH, hHd, hHq, _, _⟩ := hs.exists_extension_of_attached_disk_and_boundary
    hs hd hds hD hDs hu huq hw hab hproper hu huq hW hab hProper ed hed
    (ed.mem_subset_iff_of_extension (Homeomorph.refl u) hudu hudD hedu)
    (ed.mem_subset_iff_of_extension e hwd hWD hedw)
    (Homeomorph.refl q) hiq
    (fun x => (congrArg (fun y : D => (y : E)) (hedu x)).symm)
  have hkeep (x : w) : H ⟨x, hds (hwd x.property)⟩ =
      ⟨e x, hDs (hWD (e x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : s => (y : E)) (hHd ⟨x, hwd x.property⟩)).trans
      (congrArg (fun y : D => (y : E)) (hedw x))
  refine ⟨H, hH, fun x _ => congrArg Subtype.val (hkeep x), ?_,
    H.mem_subset_iff_of_extension e (hwd.trans hds) (hWD.trans hDs) hkeep⟩
  intro x hx
  exact hHq ⟨x, hx⟩

end Set
