import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.EndPaths
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.ConvexEndSelection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)

def spanningEndMap
    {X : Type*} [TopologicalSpace X] {R : Set X} (τ : C3 → X)
    (hτ : ContinuousOn τ tube) (hR : MapsTo τ tube R) : C(endSquare 0, R) where
  toFun z := ⟨τ z, hR ⟨z.property.1, by rw [show (z : C3).2 = 0 from z.property.2]; norm_num⟩⟩
  continuous_toFun := (hτ.comp_continuous continuous_subtype_val
    (fun z ↦ ⟨z.property.1, by rw [show (z : C3).2 = 0 from z.property.2]; norm_num⟩)).subtype_mk _

theorem spanning_end_selects_nonnull_rim
    {X : Type*} [TopologicalSpace X] {R : Set X} (τ : C3 → X)
    (hτ : ContinuousOn τ tube) (hR : MapsTo τ tube R) (sign : Bool → Bool)
    (A : Path (spanningEndMap τ hτ hR (spanningEndPoint false (sign false)))
      (spanningEndMap τ hτ hR (spanningEndPoint true (sign true))))
    (B : Path (spanningEndMap τ hτ hR (spanningEndPoint false (!(sign false))))
      (spanningEndMap τ hτ hR (spanningEndPoint true (!(sign true)))))
    (hold : ¬ (A.trans
      (((spanningOldEndPath false (sign false)).map (spanningEndMap τ hτ hR).continuous).trans
        (B.trans ((spanningOldEndPath true (sign true)).map
          (spanningEndMap τ hτ hR).continuous).symm)).symm).Homotopic
            (Path.refl (spanningEndMap τ hτ hR (spanningEndPoint false (sign false))))) :
    ¬ (A.trans ((spanningResolvingEndPath sign).map
      (spanningEndMap τ hτ hR).continuous).symm).Homotopic
        (Path.refl (spanningEndMap τ hτ hR (spanningEndPoint false (sign false)))) ∨
      ¬ (B.trans ((spanningResolvingEndPath (fun i ↦ !(sign i))).map
        (spanningEndMap τ hτ hR).continuous).symm).Homotopic
          (Path.refl (spanningEndMap τ hτ hR (spanningEndPoint false (!(sign false))))) := by
  exact convex_end_selects_nonnull_spanning_rim
    (((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).prod (convex_singleton 0))
    (spanningEndMap τ hτ hR) (spanningOldEndPath false (sign false))
    (spanningOldEndPath true (sign true)) (spanningResolvingEndPath sign)
    (spanningResolvingEndPath (fun i ↦ !(sign i))) A B hold

end PoincareConjecture.M76.Dehn
