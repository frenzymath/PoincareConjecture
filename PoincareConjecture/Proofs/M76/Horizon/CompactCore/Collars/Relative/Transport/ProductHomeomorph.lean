import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.ModelProduct
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages







set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (T : CoorientedSurfaceStars E)

local notation "I" => Icc (-1 : ℝ) 1




theorem exists_homeomorph_of_model_product {g : E × ℝ → E}
    (hg : FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I))
    (hinj : InjOn g ((T.marked 2).space ×ˢ I))
    (himage : g '' ((T.marked 2).space ×ˢ I) =
      ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}) :
    ∃ H : ((T.marked 2).space ×ˢ I) ≃ₜ
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}),
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      ∀ x : ((T.marked 2).space ×ˢ I), (H x : E) = g x := by
  have hex := hg.exists_homeomorph_image hinj
  rw [himage] at hex
  obtain ⟨H, hH, hval⟩ := hex
  exact ⟨H, hH, hH.symm, hval⟩




theorem exists_model_product_homeomorph :
    ∃ (g : E × ℝ → E)
      (H : ((T.marked 2).space ×ˢ I) ≃ₜ
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)})),
      FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I) ∧
      InjOn g ((T.marked 2).space ×ˢ I) ∧
      g '' ((T.marked 2).space ×ˢ I) =
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ x : ((T.marked 2).space ×ˢ I), (H x : E) = g x) ∧
      (∀ x ∈ (T.marked 2).space, g (x, 0) = x) ∧
      (∀ x ∈ (T.marked 2).space ×ˢ I,
        g x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space) ∧
      (∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (0 ≤ T.height p (g x) ↔ 0 ≤ x.2)) ∧
      ∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (T.height p (g x) ≤ 0 ↔ x.2 ≤ 0) := by
  obtain ⟨g, hg, hinj, himage, hcenter, hproper, hpos, hneg⟩ := T.exists_model_product
  obtain ⟨H, hH, hHinv, hval⟩ := T.exists_homeomorph_of_model_product hg hinj himage
  exact ⟨g, H, hg, hinj, himage, hH, hHinv, hval, hcenter, hproper, hpos, hneg⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars
