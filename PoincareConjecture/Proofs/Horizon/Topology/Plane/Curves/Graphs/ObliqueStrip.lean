import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Strip
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

def obliqueStripMap (A B lo : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  let x := A q.2 + q.1 * (B q.2 - A q.2)
  (x, lo x + q.2)

noncomputable def obliqueStripInv (A B lo : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  let z := q.2 - lo q.1
  ((q.1 - A z) / (B z - A z), z)

@[simp] theorem obliqueStripMap_left (A B lo : ℝ → ℝ) (z : ℝ) :
    obliqueStripMap A B lo (0, z) = (A z, lo (A z) + z) := by
  simp [obliqueStripMap]

@[simp] theorem obliqueStripMap_right (A B lo : ℝ → ℝ) (z : ℝ) :
    obliqueStripMap A B lo (1, z) = (B z, lo (B z) + z) := by
  simp [obliqueStripMap]

theorem obliqueStripMap_bottom {A B lo : ℝ → ℝ} {a b : ℝ}
    (hA : A 0 = a) (hB : B 0 = b) (t : ℝ) :
    obliqueStripMap A B lo (t, 0) = (a + t * (b - a), lo (a + t * (b - a))) := by
  simp [obliqueStripMap, hA, hB]

noncomputable def obliqueStripCoordinates
    {A B lo : ℝ → ℝ} {Z X : Set ℝ}
    (hZ : IsOpen Z) (hA : ContDiffOn ℝ ∞ A Z) (hB : ContDiffOn ℝ ∞ B Z)
    (hgap : ∀ z ∈ Z, A z < B z) (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  let S := (Homeomorph.prodComm ℝ ℝ).toOpenPartialHomeomorph
  let G := graphStripCoordinates hZ hA hB hgap
  let L := graphStripCoordinates hX hlo (hlo.add contDiffOn_const)
    (fun x _ => lt_add_one (lo x))
  ((S.trans G).trans S).trans L

section Coordinates

variable {A B lo : ℝ → ℝ} {Z X : Set ℝ}
  (hZ : IsOpen Z) (hA : ContDiffOn ℝ ∞ A Z) (hB : ContDiffOn ℝ ∞ B Z)
  (hgap : ∀ z ∈ Z, A z < B z) (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)

theorem obliqueStripCoordinates_apply (q : ℝ × ℝ) :
    obliqueStripCoordinates hZ hA hB hgap hX hlo q = obliqueStripMap A B lo q := by
  change graphStripMap lo (fun x => lo x + 1)
    ((graphStripMap A B q.swap).swap) = _
  simp [graphStripMap, obliqueStripMap]

theorem obliqueStripCoordinates_symm_apply (q : ℝ × ℝ) :
    (obliqueStripCoordinates hZ hA hB hgap hX hlo).symm q = obliqueStripInv A B lo q := by
  change (graphStripInv A B (graphStripInv lo (fun x => lo x + 1) q).swap).swap = _
  simp [graphStripInv, obliqueStripInv]

theorem obliqueStripCoordinates_source :
    (obliqueStripCoordinates hZ hA hB hgap hX hlo).source =
      {q | q.2 ∈ Z ∧ A q.2 + q.1 * (B q.2 - A q.2) ∈ X} := by
  ext q
  simp [obliqueStripCoordinates, graphStripCoordinates, graphStripMap]

theorem obliqueStripCoordinates_target :
    (obliqueStripCoordinates hZ hA hB hgap hX hlo).target =
      {q | q.1 ∈ X ∧ q.2 - lo q.1 ∈ Z} := by
  ext q
  simp [obliqueStripCoordinates, graphStripCoordinates]
  intro _
  change (q.2 - lo q.1) / (lo q.1 + 1 - lo q.1) ∈ Z ↔ q.2 - lo q.1 ∈ Z
  simp

theorem contDiffOn_obliqueStripCoordinates :
    ContDiffOn ℝ ∞ (obliqueStripCoordinates hZ hA hB hgap hX hlo)
      (obliqueStripCoordinates hZ hA hB hgap hX hlo).source := by
  rw [show (obliqueStripCoordinates hZ hA hB hgap hX hlo : (ℝ × ℝ) → ℝ × ℝ) =
    obliqueStripMap A B lo from funext (obliqueStripCoordinates_apply hZ hA hB hgap hX hlo),
    obliqueStripCoordinates_source]
  have hAc : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => A q.2)
      {q | q.2 ∈ Z ∧ A q.2 + q.1 * (B q.2 - A q.2) ∈ X} :=
    hA.comp contDiffOn_snd (fun _ hq => hq.1)
  have hBc : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B q.2)
      {q | q.2 ∈ Z ∧ A q.2 + q.1 * (B q.2 - A q.2) ∈ X} :=
    hB.comp contDiffOn_snd (fun _ hq => hq.1)
  have hx := hAc.add (contDiffOn_fst.mul (hBc.sub hAc))
  exact hx.prodMk ((hlo.comp hx (fun _ hq => hq.2)).add contDiffOn_snd)

theorem contDiffOn_obliqueStripCoordinates_symm :
    ContDiffOn ℝ ∞ (obliqueStripCoordinates hZ hA hB hgap hX hlo).symm
      (obliqueStripCoordinates hZ hA hB hgap hX hlo).target := by
  rw [show ((obliqueStripCoordinates hZ hA hB hgap hX hlo).symm :
      (ℝ × ℝ) → ℝ × ℝ) = obliqueStripInv A B lo from
    funext (obliqueStripCoordinates_symm_apply hZ hA hB hgap hX hlo),
    obliqueStripCoordinates_target]
  have hz : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.2 - lo q.1)
      {q | q.1 ∈ X ∧ q.2 - lo q.1 ∈ Z} :=
    contDiffOn_snd.sub (hlo.comp contDiffOn_fst (fun _ hq => hq.1))
  have hAc := hA.comp hz (fun _ hq => hq.2)
  have hBc := hB.comp hz (fun _ hq => hq.2)
  exact ((contDiffOn_fst.sub hAc).div (hBc.sub hAc)
    (fun q hq => ne_of_gt (sub_pos.mpr (hgap _ hq.2)))).prodMk hz

end Coordinates

theorem obliqueStripMap_image_rectangle {A B lo : ℝ → ℝ} {u v : ℝ}
    (hgap : ∀ z ∈ Icc u v, A z < B z) :
    obliqueStripMap A B lo '' (Icc (0 : ℝ) 1 ×ˢ Icc u v) =
      {q | q.2 - lo q.1 ∈ Icc u v ∧
        A (q.2 - lo q.1) ≤ q.1 ∧ q.1 ≤ B (q.2 - lo q.1)} := by
  ext q
  constructor
  · rintro ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
    simp only [mem_ofPred_eq, obliqueStripMap, add_sub_cancel_left]
    have h := hgap z hz
    exact ⟨hz, by nlinarith [mul_nonneg ht.1 (sub_pos.mpr h).le],
      by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr h).le]⟩
  · rintro ⟨hz, hleft, hright⟩
    let z := q.2 - lo q.1
    have hg : 0 < B z - A z := sub_pos.mpr (hgap z hz)
    refine ⟨((q.1 - A z) / (B z - A z), z), ⟨?_, hz⟩, ?_⟩
    · exact ⟨div_nonneg (sub_nonneg.mpr hleft) hg.le,
        (div_le_one hg).mpr (sub_le_sub_right hright _)⟩
    · have he : A z + ((q.1 - A z) / (B z - A z)) * (B z - A z) = q.1 := by
        rw [div_mul_cancel₀ _ hg.ne']
        ring
      simp only [obliqueStripMap, he]
      dsimp [z]
      simp

end Poincare.Topology.Plane.Curves
