import PoincareConjecture.Proofs.M76.Rigidity.OriginalProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarCofaces
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem exists_edge_chart_sign_witnesses
    (p : (T.marked 2).vertices) {s t : Finset (T.index → ℝ × V3)}
    (hps : (p : T.index → ℝ × V3) ∈ s) (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) (ht : t ∈ T.ambient.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (A : C3 →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hzero : ∀ x ∈ t, A (T.chart (T.chart_index p) (T.inverse x)) = 0) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
      t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
      u.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      v.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      A (T.chart (T.chart_index p) (T.inverse (u.centroid ℝ id))) < 0 ∧
      0 < A (T.chart (T.chart_index p) (T.inverse (v.centroid ℝ id))) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let f : (T.index → ℝ × V3) → C3 := fun x => T.chart (T.chart_index p) (T.inverse x)
  have h3 : Module.finrank ℝ C3 = 3 := by simp [Module.finrank_prod]
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, huv, _⟩ :=
    T.ambient.exists_paired_facet_of_embedded_star T.finite ht
      (htcard.trans h3.symm) (hst hps) f
      (T.star_affine p) (T.star_injective p) (T.star_interior p)
  have huc' : u.card = 4 := by simpa only [h3] using huc
  have hvc' : v.card = 4 := by simpa only [h3] using hvc
  have hstar {w : Finset (T.index → ℝ × V3)}
      (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) :
      w ∈ (T.ambient.closedStar p).faces :=
    ⟨hw, by simpa only [Finset.insert_eq_of_mem (htw (hst hps))] using hw⟩
  have hsign := (T.star_affine p).opposite_centroid_signs
    (T.star_injective p) (hstar ht Subset.rfl) (hstar hu htu) (hstar hv htv)
    (htcard.trans h3.symm) huc hvc htu htv huv A hA hzero
  have hmark {w : Finset (T.index → ℝ × V3)}
      (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) (hwc : w.card = 4) :
      w.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space := by
    apply T.ambient.cofaceCentroid_mem_dualBlock_link (T.marked_le 2 hs) hw (hst.trans htw)
    intro he
    rw [he, hwc] at hscard
    omega
  rcases hsign with h | h
  · exact ⟨u, hu, v, hv, htu, htv, huc', hvc', hmark hu htu huc',
      hmark hv htv hvc', h.1, h.2⟩
  · exact ⟨v, hv, u, hu, htv, htu, hvc', huc', hmark hv htv hvc',
      hmark hu htu huc', h.2, h.1⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
