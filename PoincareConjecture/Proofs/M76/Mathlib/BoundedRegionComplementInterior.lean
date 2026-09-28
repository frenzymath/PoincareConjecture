import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall











set_option autoImplicit false

open Set Geometry

namespace Set





theorem interior_closure_sdiff_of_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {B s : Set X}
    (hB : IsClosed B) (hs : closure (interior s) = s) :
    interior (closure (B \ s)) = interior B \ s := by
  have hclosed : IsClosed s := hs ▸ isClosed_closure
  have hCB : closure (B \ s) ⊆ B := closure_minimal sdiff_subset hB
  have havoid : closure (B \ s) ⊆ (interior s)ᶜ :=
    closure_minimal (fun _ hx hxi => hx.2 (interior_subset hxi))
      isOpen_interior.isClosed_compl
  have hinter := interior_mono havoid
  rw [interior_compl, hs] at hinter
  apply Subset.antisymm
  · exact fun _ hx => ⟨interior_mono hCB hx, hinter hx⟩
  · exact interior_maximal
      (fun _ hx => subset_closure ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.sdiff hclosed)

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem IsFinitePLBallPair.of_prod_singleton {s b : Set E} {z : F}
    (hs : IsFinitePLBallPair V (s ×ˢ {z}) (b ×ˢ {z})) :
    IsFinitePLBallPair V s b := by
  let a : E × F →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap
  have ha : InjOn a (s ×ˢ {z}) := by
    intro x hx y hy hxy
    exact Prod.ext hxy ((mem_singleton_iff.mp hx.2).trans
      (mem_singleton_iff.mp hy.2).symm)
  have hball := hs.affine_image a ha
  change IsFinitePLBallPair V (Prod.fst '' (s ×ˢ {z}))
    (Prod.fst '' (b ×ˢ {z})) at hball
  simpa only [fst_image_prod _ (singleton_nonempty z)] using hball

end Set
