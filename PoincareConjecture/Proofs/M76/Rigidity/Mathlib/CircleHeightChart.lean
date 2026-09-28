import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNonvertexHeightChart
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_centered_circle_height_chart
    {M E ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (p : ℝ) [Fact (0 < p)] (q : M → AddCircle p)
    (i : ι) (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : K.AffineOnFaces w) {x : M}
    (hx : x ∈ (e i).source) (hxK : e i x ∈ interior K.space)
    (hlift : ∀ z ∈ K.space, q ((e i).symm z) = (w z : AddCircle p))
    (hreg : ∀ z ∈ K.vertices, w z ≠ w (e i x)) :
    ∃ (a : ℝ) (ell : E →ᴬ[ℝ] ℝ) (v : E) (G : OpenPartialHomeomorph M E),
      (a : AddCircle p) = q x ∧ ell.contLinear v = 1 ∧
      x ∈ G.source ∧ ell (G x) = 0 ∧
      (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      (∀ y ∈ G.source, q y = ((ell (G y) + a : ℝ) : AddCircle p)) ∧
      ∀ y ∈ G.source, q y = q x ↔ ell (G y) = 0 := by
  obtain ⟨ell, v, H, hell, hxH, _, hHs, _, hHPL, hheight⟩ :=
    K.exists_nonvertex_height_chart hK hw hxK hreg
  let a := w (e i x)
  let W : Set E := ell ⁻¹' Ioo (a - p / 2) (a + p / 2)
  have hW : IsOpen W := isOpen_Ioo.preimage ell.continuous
  let I := OpenPartialHomeomorph.ofSet W hW
  let G := ((e i).trans H).trans I
  let ell0 := ell - ContinuousAffineMap.const ℝ E a
  have hp : 0 < p := Fact.out
  have hax : (a : AddCircle p) = q x := by
    have h := hlift (e i x) (interior_subset hxK)
    rw [(e i).left_inv hx] at h
    exact h.symm
  have hxG : x ∈ G.source := by
    refine ⟨⟨hx, hxH⟩, ?_⟩
    change ell (H (e i x)) ∈ Ioo (a - p / 2) (a + p / 2)
    rw [hheight _ hxH]
    change a - p / 2 < a ∧ a < a + p / 2
    constructor <;> linarith
  have hell0 : ell0.contLinear v = 1 := by
    simpa only [ell0, ContinuousAffineMap.sub_contLinear,
      ContinuousAffineMap.const_contLinear, sub_zero] using hell
  have hI : I ∈ piecewiseAffineGroupoid E := by
    exact ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW,
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW⟩
  have hq (y : M) (hy : y ∈ G.source) :
      q y = ((ell (G y) : ℝ) : AddCircle p) := by
    have h := hlift (e i y) (interior_subset (hHs hy.1.2))
    rw [(e i).left_inv hy.1.1] at h
    change q y = ((ell (H (e i y)) : ℝ) : AddCircle p)
    rw [hheight (e i y) hy.1.2]
    exact h
  refine ⟨a, ell0, v, G, hax, hell0, hxG, ?_, ?_, ?_, ?_⟩
  · change ell (H (e i x)) - a = 0
    rw [hheight _ hxH]
    exact sub_self a
  · intro j
    simpa only [G, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans
        ((piecewiseAffineGroupoid E).trans (hcompat j i) hHPL) hI
  · intro y hy
    change q y = ((ell (G y) - a + a : ℝ) : AddCircle p)
    simpa only [sub_add_cancel] using hq y hy
  · intro y hy
    have hyW : ell (G y) ∈ Ioo (a - p / 2) (a + p / 2) := hy.2
    have hyI : ell (G y) ∈ Ico (a - p / 2) (a - p / 2 + p) := by
      exact ⟨hyW.1.le, by linarith [hyW.2]⟩
    have haI : a ∈ Ico (a - p / 2) (a - p / 2 + p) := by
      constructor <;> linarith
    rw [hq y hy, ← hax, AddCircle.coe_eq_coe_iff_of_mem_Ico hyI haI]
    change ell (G y) = a ↔ ell (G y) - a = 0
    exact sub_eq_zero.symm

end OpenPartialHomeomorph
