import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk
import PoincareConjecture.Proofs.M76.Mathlib.RelativeTwoBallSideExtension

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_boundary_extension_fix_attached_disk
    {s q d u w : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (u ∪ w)) (hds : d ⊆ s)
    (hu : IsFinitePLBallPair ℝ u {a, b}) (huq : u ⊆ q)
    (hw : IsFinitePLBallPair ℝ w {a, b}) (hab : a ≠ b)
    (hproper : w \ {a, b} ⊆ s \ q)
    (g : q ≃ₜ q) (hg : g.IsFinitePL)
    (hfix : ∀ x : q, (x : E) ∈ u → g x = x) :
    ∃ H : s ≃ₜ s, H.IsFinitePL ∧
      (∀ x : s, (x : E) ∈ d → H x = x) ∧
      (∀ x : q, H ⟨x, hs.1 x.property⟩ = ⟨g x, hs.1 (g x).property⟩) ∧
      ∀ x : s, (x : E) ∈ q ↔ (H x : E) ∈ q := by
  obtain ⟨v, hv, hq, huv, hc, hunion, hinter, _, _⟩ :=
    hs.exists_boundary_attached_disk_complement hd hds hu huq hw hab hproper
  let c := s \ (d \ w)
  have hvq : v ⊆ q := subset_union_right.trans hq.subset
  have hmem (z : Set E) (hzu : z ⊆ u) (x : q) :
      (x : E) ∈ z ↔ (g x : E) ∈ z := by
    constructor
    · intro hx
      rw [hfix x (hzu hx)]
      exact hx
    · intro hx
      have heq : g x = x := g.injective (hfix (g x) (hzu hx))
      rwa [heq] at hx
  have htest (x : q) : (x : E) ∈ v ↔
      (x : E) ∉ u ∨ (x : E) ∈ ({a, b} : Set E) := by
    have hcover : (x : E) ∈ u ∨ (x : E) ∈ v := hq.symm.subset x.property
    have hcommon : ((x : E) ∈ u ∧ (x : E) ∈ v) ↔
        (x : E) ∈ ({a, b} : Set E) := Set.ext_iff.mp huv x
    tauto
  have hmemv (x : q) : (x : E) ∈ v ↔ (g x : E) ∈ v :=
    (htest x).trans ((or_congr (not_congr (hmem u subset_rfl x))
      (hmem {a, b} hu.1 x)).trans (htest (g x)).symm)
  let gv := g.restrictSubsets hvq hvq hmemv
  have hvcopy := hv
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKv, _⟩, _⟩, _⟩ := hvcopy
  have hgv : gv.IsFinitePL := hg.restrictSubsets hvq hvq hmemv K hK hKv
  have hwv : w ∩ v = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxp
      exact (hproper ⟨hx.1, hxp⟩).2 (hvq hx.2)
    · intro x hx
      exact ⟨hw.1 hx, hv.1 hx⟩
  have hgvfix (x : v) (hx : (x : E) ∈ ({a, b} : Set E)) : gv x = x :=
    Subtype.ext (congrArg (fun y : q => (y : E))
      (hfix ⟨x, hvq x.property⟩ (hu.1 hx)))
  obtain ⟨ec, hec, hecw, hecv, _⟩ :=
    hc.exists_extension_fix_outer_piece hw hwv gv hgv hgvfix
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJd, _⟩, _⟩, _⟩ := hdcopy
  have hid : (Homeomorph.refl d).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJd, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,
      fun _ => rfl⟩
  have hagree (x : E) (hxd : x ∈ d) (hxc : x ∈ c) :
      ((Homeomorph.refl d) ⟨x, hxd⟩ : E) = (ec ⟨x, hxc⟩ : E) := by
    have hxw : x ∈ w := hinter ▸ And.intro hxd hxc
    exact (congrArg Subtype.val (hecw ⟨x, hxw⟩)).symm
  obtain ⟨H₀, hH₀, hH₀d, hH₀c⟩ := Homeomorph.exists_union_finitePL
    (Homeomorph.refl d) ec hid hec (fun _ => Iff.rfl) hagree
  let H : s ≃ₜ s := (Homeomorph.setCongr hunion.symm).trans
    (H₀.trans (Homeomorph.setCongr hunion))
  have hH : H.IsFinitePL := by
    obtain ⟨f, hf, hHf⟩ := hH₀
    rw [hunion] at hf
    exact ⟨f, hf, fun x => hHf ⟨x, hunion.symm ▸ x.property⟩⟩
  have hkeepd (x : s) (hx : (x : E) ∈ d) : H x = x :=
    Subtype.ext (hH₀d ⟨x, hx⟩)
  have hkeepq (x : q) : H ⟨x, hs.1 x.property⟩ =
      ⟨g x, hs.1 (g x).property⟩ := by
    apply Subtype.ext
    rcases hq.symm.subset x.property with hxu | hxv
    · exact (congrArg Subtype.val
        (hkeepd ⟨x, hs.1 x.property⟩ (hd.1 (Or.inl hxu)))).trans
          (congrArg Subtype.val (hfix x hxu)).symm
    · exact (hH₀c ⟨x, hc.1 (Or.inr hxv)⟩).trans
        (congrArg Subtype.val (hecv ⟨x, hxv⟩))
  exact ⟨H, hH, hkeepd, hkeepq,
    H.mem_subset_iff_of_extension g hs.1 hs.1 hkeepq⟩

end Set
