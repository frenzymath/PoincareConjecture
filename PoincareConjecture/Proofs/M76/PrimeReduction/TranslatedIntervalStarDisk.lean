import PoincareConjecture.Proofs.M76.PrimeReduction.IntervalLinkClosedStarDisk
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem isFinitePLBallPair_closedStar_of_interval
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p a b : E} (hp : p ∈ K.vertices)
    (hI : IsFinitePLBallPair ℝ (K.link p).space {a, b}) :
    IsFinitePLBallPair (ℝ × ℝ) (K.closedStar p).space
      ((K.link p).space ∪ convexJoin ℝ {p} {a, b}) := by
  classical
  let t : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have htp : t p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hti0 : t.symm 0 = p := by rw [← htp, t.symm_apply_apply]
  let hf := K.affineOnFaces_affine t.toContinuousAffineMap
  let J := hf.embeddedImage t.injective.injOn
  have hJ : J.faces.Finite := hf.embeddedImage_finite t.injective.injOn hK
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
  have hIJ : IsFinitePLBallPair ℝ (J.link 0).space {t a, t b} := by
    rw [hJlink]
    have h := hI.affine_image t.toContinuousAffineMap t.injective.injOn
    change IsFinitePLBallPair ℝ (t '' (K.link p).space) (t '' {a, b}) at h
    simpa only [image_pair] using h
  have hball := J.isFinitePLBallPair_closedStar_zero_of_interval hJ hzJ hIJ
  have hback (S : Set E) : t.symm '' (t '' S) = S := by simp
  have hcone : t.symm '' convexJoin ℝ {(0 : E)} {t a, t b} =
      convexJoin ℝ {p} {a, b} := by
    change t.symm.toAffineEquiv.toAffineMap '' convexJoin ℝ {(0 : E)} {t a, t b} = _
    rw [AffineMap.image_convexJoin]
    change convexJoin ℝ (t.symm '' {(0 : E)}) (t.symm '' {t a, t b}) = _
    simp only [image_singleton, image_pair, hti0, t.symm_apply_apply]
  have himage := hball.affine_image t.symm.toContinuousAffineMap t.symm.injective.injOn
  change IsFinitePLBallPair (ℝ × ℝ) (t.symm '' (J.closedStar 0).space)
    (t.symm '' ((J.link 0).space ∪ convexJoin ℝ {0} {t a, t b})) at himage
  simpa only [image_union, hJstar, hJlink, hback, hcone] using himage

end Geometry.SimplicialComplex
