import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.NormalizedBoundary

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_band_and_halfspace_avoidance
    {v : E3} {b c : Real} (hbc : b < c)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {band : Set E3} {R : Real} (hR : 0 < R)
    (havoid : ∀ y ∈ band, inner Real v y ≤ b + 2 * R →
      (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∉ A '' ball 0 1) :
    ∃ w : Real, 0 < w ∧ w ≤ R ∧ b + 2 * w < c ∧
      ∀ y ∈ band ∪ {y | c ≤ inner Real v y}, inner Real v y ≤ b + 2 * w →
        (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∉ A '' ball 0 1 := by
  let w := min R ((c - b) / 4)
  have hw : 0 < w := lt_min hR (by positivity)
  have hwR : w ≤ R := min_le_left _ _
  have hwc : b + 2 * w < c := by
    have hh : w ≤ (c - b) / 4 := min_le_right _ _
    linarith
  refine ⟨w, hw, hwR, hwc, ?_⟩
  intro y hy hh
  rcases hy with hy | hy
  · exact havoid y hy (by linarith)
  · exact (hwc.not_ge (hy.trans hh)).elim

theorem disjoint_projected_cylindrical_rims
    {ι κ : Type*} {v : E3} {b : Real}
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (surface : ι → Set E3) (hdis : Pairwise (fun i j => Disjoint (surface i) (surface j)))
    (rim : ι → κ → E3)
    (hmem : ∀ i q, rim i q ∈ surface i)
    (hcyl : ∀ i q, Q (rim i q) = b • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto (rim i q) : E3)) :
    Pairwise (fun i j => Disjoint
      (range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (rim i q)))
      (range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (rim j q)))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨q, hq⟩ ⟨r, hr⟩
  dsimp only at hq hr
  have heq : rim i q = rim j r := Q.injective (by
    change Q (rim i q) = Q (rim j r)
    rw [hcyl, hcyl, hq, hr])
  exact disjoint_left.mp (hdis hij) (hmem i q) (heq ▸ hmem j r)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
