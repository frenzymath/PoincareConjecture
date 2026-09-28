import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.Topology.Algebra.ContinuousAffineEquiv










set_option autoImplicit false

open Set

namespace Set

variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]






theorem IsFinitePLBallPair.affine_cylinderExterior
    {C B b : Set E} {D : Set ℝ} {z : ℝ}
    (hball : IsFinitePLBallPair V (frontier (C ×ˢ D) \ interior B ×ˢ {z})
      (b ×ˢ {z})) (e : E ≃ᴬ[ℝ] F) :
    IsFinitePLBallPair V
      (frontier ((e '' C) ×ˢ D) \ interior (e '' B) ×ˢ {z}) ((e '' b) ×ˢ {z}) := by
  let G := e.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)
  have hprod (s : Set E) (t : Set ℝ) : G '' (s ×ˢ t) = (e '' s) ×ˢ t := by
    change Prod.map e id '' (s ×ˢ t) = (e '' s) ×ˢ t
    rw [prodMap_image_prod, image_id]
  have hfront : G '' frontier (C ×ˢ D) = frontier ((e '' C) ×ˢ D) :=
    (G.toHomeomorph.image_frontier (C ×ˢ D)).trans (congrArg frontier (hprod C D))
  have hinter : e '' interior B = interior (e '' B) := e.toHomeomorph.image_interior B
  have hcarrier : G '' (frontier (C ×ˢ D) \ interior B ×ˢ {z}) =
      frontier ((e '' C) ×ˢ D) \ interior (e '' B) ×ˢ {z} := by
    rw [image_sdiff G.injective, hfront, hprod, hinter]
  have himage := hball.affine_image G.toContinuousAffineMap G.injective.injOn
  change IsFinitePLBallPair V (G '' (frontier (C ×ˢ D) \ interior B ×ˢ {z}))
    (G '' (b ×ˢ {z})) at himage
  rwa [hcarrier, hprod] at himage

end Set
