import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Duals

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (T : CoorientedSurfaceStars E)

def height (p : (T.marked 2).vertices) (x : E) : ℝ := (T.chart p x).2

theorem height_affine (p : (T.marked 2).vertices) :
    (T.ambient.closedStar p).AffineOnFaces (T.height p) :=
  (T.star_affine p).postcomp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap

theorem continuousOn_height_star (p : (T.marked 2).vertices) :
    ContinuousOn (T.height p) (T.ambient.closedStar p).space :=
  (T.height_affine p).continuousOn (finite_closedStar_faces T.finite p)

theorem continuousOn_height_dualRegion (p : (T.marked 2).vertices)
    {s : Finset E} (hps : (p : E) ∈ s) : ContinuousOn (T.height p) (T.dualRegion s) :=
  (T.continuousOn_height_star p).mono (T.dualRegion_subset_star p hps)

theorem height_eq_zero_iff (p : (T.marked 2).vertices) {x : E}
    (hx : x ∈ (T.ambient.closedStar p).space) (hxR : x ∈ (T.marked 0).space) :
    T.height p x = 0 ↔ x ∈ (T.marked 2).space := by
  exact ⟨fun h => (T.surface_eq p x hx).mpr ⟨hxR, h⟩,
    fun h => ((T.surface_eq p x hx).mp h).2⟩

theorem height_eq_zero_iff_on_dualRegion (p : (T.marked 2).vertices)
    {s : Finset E} (hps : (p : E) ∈ s) {x : E} (hx : x ∈ T.dualRegion s) :
    T.height p x = 0 ↔ x ∈ (T.marked 2).space :=
  T.height_eq_zero_iff p (T.dualRegion_subset_star p hps hx) hx.2

theorem dualRegion_halves_eq (p q : (T.marked 2).vertices)
    {s : Finset E} (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s) :
    (T.dualRegion s ∩ {x | 0 ≤ T.height p x} =
      T.dualRegion s ∩ {x | 0 ≤ T.height q x}) ∧
    (T.dualRegion s ∩ {x | T.height p x ≤ 0} =
      T.dualRegion s ∩ {x | T.height q x ≤ 0}) := by
  constructor
  · ext x
    exact and_congr_right (fun hx => T.nonneg_agree p q x
      (T.dualRegion_subset_star p hps hx) (T.dualRegion_subset_star q hqs hx))
  · ext x
    exact and_congr_right (fun hx => T.nonpos_agree p q
      (T.dualRegion_subset_star p hps hx) (T.dualRegion_subset_star q hqs hx))

end Geometry.SimplicialComplex.CoorientedSurfaceStars
