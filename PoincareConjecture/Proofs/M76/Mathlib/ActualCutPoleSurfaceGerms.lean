import PoincareConjecture.Proofs.M76.Mathlib.AffinePlaneGermRigidity
import PoincareConjecture.Proofs.M76.Mathlib.ActualRadialFrontierPoles
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexFrontier

set_option autoImplicit false

open Set NormedSpace CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

theorem mem_closedStar_of_frontier_positive_smul
    (K : SimplicialComplex ℝ E) {C : Set E}
    (hC : IsClosed C) (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    (hlink : Disjoint C (K.link 0).space)
    {a p : E} (ha : a ∈ (K.closedStar 0).space) (hp : p ∈ frontier C)
    {ρ : ℝ} (hρ : 0 < ρ) (hpa : p = ρ • a) : p ∈ (K.closedStar 0).space := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hp0 : p = 0 := by rw [hpa, ha0, smul_zero]
    exact hp.2 (by simpa only [hp0] using hzero)
  obtain ⟨y, hy, t, ht, hay⟩ := exists_linkPoint_smul ha ha0
  have hdir : normalize y = normalize p := by
    rw [hpa, normalize_smul_of_pos hρ, hay, normalize_smul_of_pos ht.1]
  have hpsection : p ∈ (K.closedStar 0).space ∩ frontier C := by
    rw [← K.radial_frontier_section_eq_closedStar_inter hC hcv hzero hlink]
    exact ⟨hp, y, hy, hdir⟩
  exact hpsection.1

theorem exists_actual_cut_pole_surface_germ
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hastar : a ∈ (K.closedStar 0).space)
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hf0 : f 0 = a)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hlast : ∀ x : (ℝ × ℝ) × ℝ, (e (f x)).2 = x.2)
    {σ : ℝ} (hσ : σ ≠ 0) (hea : e a = ((0, σ), 0))
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hlink : Disjoint C (K.link 0).space)
    (haC : a ∈ C) :
    ∃ (p : E) (ρ : ℝ) (U : Set E),
      p ∈ frontier C ∧ p ∈ (K.closedStar 0).space ∧
      (0 : E) ∈ s ∧ p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      1 ≤ ρ ∧ p = ρ • a ∧ e p = ((0, ρ * σ), 0) ∧ ρ * σ ≠ 0 ∧
      (a ∈ interior C → 1 < ρ) ∧ IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, x ∈ K.space ↔ (e x).2 = 0 := by
  obtain ⟨p, ρ, hpC, hρ, hpa, hep, hρσ, hstrict⟩ :=
    hC.exists_frontier_radial_pole_of_linear_image hcv hzero e haC hσ hea
  have hpstar := K.mem_closedStar_of_frontier_positive_smul
    hC.isClosed hcv hzero hlink hastar hpC (zero_lt_one.trans_le hρ) hpa
  have hpface := K.zero_mem_and_mem_triangle_interior_of_radial_frontier
    hbound hs hcard ha hC.isClosed hlink hpC hpstar hρ hpa
  obtain ⟨U, hU, hpU, hsurface⟩ := K.exists_open_surface_eq_last_at_radial_frontier
    hK hbound hs hcard ha f hf0 hr hcarrier e hlast hC.isClosed hlink hpC hpstar hρ hpa
  exact ⟨p, ρ, U, hpC, hpstar, hpface.1, hpface.2,
    hρ, hpa, hep, hρσ, hstrict, hU, hpU, hsurface⟩

end Geometry.SimplicialComplex
