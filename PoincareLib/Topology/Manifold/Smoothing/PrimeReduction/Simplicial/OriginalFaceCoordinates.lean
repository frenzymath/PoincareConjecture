import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Simplicial.ReturningFaceCoordinates

/-!
# The fixed face and edge produce their own plane coordinates

The two marked edge vertices and the one remaining face vertex
construct the same affine chart. All carriers refer to the original
coarse complex. See Kneser1929 p.254 and Prime016, section8.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual coarse face and its marked edge construct both affine
coordinates, their full hull images and the supporting-axis test.
Vertex labels and plane maps are outputs of the construction.
See Prime016, section8. -/
theorem exists_original_face_coordinates
    {K : SimplicialComplex ℝ E} {s e : Finset E}
    (hs : s ∈ K.faces) (hsc : s.card = 3) (hec : e.card = 2) (hes : e ⊆ s) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ)),
      Function.LeftInverse R F ∧ EqOn (F ∘ R) id (affineSpan ℝ (s : Set E)) ∧
      F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (s : Set E) ∧
      F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (e : Set E) ∧
      R '' convexHull ℝ (s : Set E) = convexHull ℝ (range rightTriangle) ∧
      (∀ z, F z ∈ convexHull ℝ (e : Set E) → z.2 = 0) ∧
      ∀ x ∈ convexHull ℝ (s : Set E), 0 ≤ (R x).2 := by
  classical
  obtain ⟨v0, v1, h01, he⟩ := Finset.card_eq_two.mp hec
  have hcard : e.card < s.card := by omega
  obtain ⟨v2, hv2⟩ := Finset.sdiff_nonempty_of_card_lt_card hcard
  obtain ⟨hv2s, hv2e⟩ := Finset.mem_sdiff.mp hv2
  have hv0e : v0 ∈ e := by rw [he]; simp
  have hv1e : v1 ∈ e := by rw [he]; simp
  have h02 : v0 ≠ v2 := fun h => hv2e (h ▸ hv0e)
  have h12 : v1 ≠ v2 := fun h => hv2e (h ▸ hv1e)
  have hsub : ({v0, v1, v2} : Finset E) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact h.symm ▸ hes hv0e
    · exact h.symm ▸ hes hv1e
    · exact h.symm ▸ hv2s
  have hsEq : s = {v0, v1, v2} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hsc, h01, h02, h12])).symm
  have hs' : ({v0, v1, v2} : Finset E) ∈ K.faces := hsEq ▸ hs
  obtain ⟨F, R, hleft, hright, _, _, _, hface, hedge, hRface, haxis⟩ :=
    exists_returning_face_coordinates h01 h02 h12 hs'
  have hset : (s : Set E) = {v0, v1, v2} := by rw [hsEq]; simp
  have heset : (e : Set E) = {v0, v1} := by rw [he]; simp
  refine ⟨F, R, hleft, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hset] using hright
  · simpa only [hset] using hface
  · simpa only [heset] using hedge
  · simpa only [hset] using hRface
  · simpa only [heset] using haxis
  · intro x hx
    have hRx : R x ∈ convexHull ℝ (range rightTriangle) :=
      hRface.subset ⟨x, hset ▸ hx, rfl⟩
    exact ((mem_right_region_iff (R x)).mp hRx).2.1

end Geometry.SimplicialComplex
