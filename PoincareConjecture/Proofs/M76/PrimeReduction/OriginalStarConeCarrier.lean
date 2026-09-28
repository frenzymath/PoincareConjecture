import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem closedStar_space_eq_convexJoin_link (K : SimplicialComplex ℝ E)
    {p : E} (hp : p ∈ K.vertices) (hne : (K.link p).space.Nonempty) :
    (K.closedStar p).space = convexJoin ℝ {p} (K.link p).space := by
  classical
  let t : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have htp : t p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hti0 : t.symm 0 = p := by rw [← htp, t.symm_apply_apply]
  let hf := K.affineOnFaces_affine t.toContinuousAffineMap
  let J := hf.embeddedImage t.injective.injOn
  have hJstar : (J.closedStar 0).space = t '' (K.closedStar p).space := by
    have h := hf.embeddedImage_closedStar_space t.injective.injOn hp
    change (J.closedStar (t p)).space = t '' (K.closedStar p).space at h
    simpa only [htp] using h
  have hJlink : (J.link 0).space = t '' (K.link p).space := by
    have h := hf.embeddedImage_link_space t.injective.injOn hp
    change (J.link (t p)).space = t '' (K.link p).space at h
    simpa only [htp] using h
  have hzJ : (0 : E) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices t.injective.injOn]
    exact ⟨p, hp, htp⟩
  have hconeJ : (J.closedStar 0).space = convexJoin ℝ {0} (J.link 0).space := by
    rw [← coneAtZero_link_eq_closedStar J hzJ]
    exact (J.link 0).coneAtZero_space_eq_convexJoin _ _ (hJlink.symm ▸ hne.image t)
  have hback (S : Set E) : t.symm '' (t '' S) = S := by simp
  calc
    (K.closedStar p).space = t.symm '' (J.closedStar 0).space := by rw [hJstar, hback]
    _ = t.symm '' convexJoin ℝ {0} (J.link 0).space := congrArg (image t.symm) hconeJ
    _ = convexJoin ℝ {p} (K.link p).space := by
      change t.symm.toAffineEquiv.toAffineMap '' convexJoin ℝ {(0 : E)} (J.link 0).space = _
      rw [AffineMap.image_convexJoin]
      change convexJoin ℝ (t.symm '' {(0 : E)}) (t.symm '' (J.link 0).space) = _
      rw [image_singleton, hti0, hJlink, hback]

end Geometry.SimplicialComplex
