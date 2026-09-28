import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideIntegrals
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.AdjacentFaces

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Interval

namespace PoincareConjecture.Topology.Surface

def triangleSidePermutation (i : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.addRight (-(i + 1))

@[simp] theorem triangleSidePermutation_symm_zero (i : Fin 3) :
    (triangleSidePermutation i).symm 0 = i + 1 := by
  simp [triangleSidePermutation, Equiv.addRight]

@[simp] theorem triangleSidePermutation_symm_two (i : Fin 3) :
    (triangleSidePermutation i).symm 2 = i := by
  fin_cases i <;> norm_num [triangleSidePermutation, Equiv.addRight, Fin.add_def, Fin.neg_def]
  rfl

theorem triangleSidePermutation_orientation (i : Fin 3) :
    trianglePermutationOrientation (triangleSidePermutation i) = 1 :=
  trianglePermutationOrientation_cyclic _

private theorem side_successor_ne (i : Fin 3) : i ≠ i + 1 := by
  fin_cases i <;> decide

private theorem lineMap_image_swap {S : Type*} (F : EuclideanSpace ℝ (Fin 2) → S)
    (p q : EuclideanSpace ℝ (Fin 2)) :
    (fun t : ℝ => F (AffineMap.lineMap q p t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => F (AffineMap.lineMap p q t)) '' Icc (0 : ℝ) 1 := by
  apply subset_antisymm
  all_goals
    rintro x ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    dsimp only
    rw [AffineMap.lineMap_apply_one_sub]

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem coordinateTriangleTurningIntegral_pair_eq_zero
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart G c))
    (i j : Fin 3)
    (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b (i + 1)) t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => G (AffineMap.lineMap (c j) (c (j + 1)) t)) '' Icc (0 : ℝ) 1)
    (hdisjoint : Disjoint (interior (F '' convexHull ℝ (range b)))
      (interior (G '' convexHull ℝ (range c)))) :
    coordinateTriangleTurningIntegral D F b Q i (i + 1) +
      coordinateTriangleTurningIntegral D G c R j (j + 1) = 0 := by
  let r := triangleSidePermutation i
  let s := triangleSidePermutation j
  let b' := b.reindex r
  let c' := c.reindex s
  have hbr : convexHull ℝ (range b') = convexHull ℝ (range b) := by
    simp only [b', AffineBasis.coe_reindex, EquivLike.range_comp]
  have hcr : convexHull ℝ (range c') = convexHull ℝ (range c) := by
    simp only [c', AffineBasis.coe_reindex, EquivLike.range_comp]
  let Q' := g.alignedChartFrame (coordinateTriangleChart F b')
    (coordinateTriangleChart_smooth F b' hFi) (coordinateTriangleChart_smooth_symm F b' hF)
  let R' := g.alignedChartFrame (coordinateTriangleChart G c')
    (coordinateTriangleChart_smooth G c' hGi) (coordinateTriangleChart_smooth_symm G c' hG)
  have himage' : (fun t : ℝ => G (AffineMap.lineMap (c' 0) (c' 2) t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => F (AffineMap.lineMap (b' 0) (b' 2) t)) '' Icc (0 : ℝ) 1 := by
    simp only [b', c', AffineBasis.reindex_apply, r, s,
      triangleSidePermutation_symm_zero, triangleSidePermutation_symm_two]
    rw [lineMap_image_swap G (c j) (c (j + 1)), lineMap_image_swap F (b i) (b (i + 1))]
    exact himage.symm
  have hcancel := integral_coordinateTriangle_shared_vertical_side_pair_eq_zero D F G b' c'
    hF hFi hG hGi (hbr ▸ hb) (hcr ▸ hc) Q' R' himage' (by rwa [hbr, hcr])
  have hvertical (H : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
      (d : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
      coordinateTriangleSideField H d 0 2 = coordinateTriangleSecondField H d := by
    funext x
    simp [coordinateTriangleSideField, coordinateTriangleSecondField, standardTriangleVertex]
  have hunit (H : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
      (d : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
      coordinateTriangleSideUnitField g H d 0 2 = coordinateTriangleSecondUnitField g H d := by
    funext x
    simp only [coordinateTriangleSideUnitField, hvertical, coordinateTriangleSecondUnitField]
  have heq : coordinateTriangleTurningIntegral D G c' R' 0 2 +
      coordinateTriangleTurningIntegral D F b' Q' 0 2 = 0 := by
    simpa only [coordinateTriangleTurningIntegral, hunit, hvertical] using hcancel
  rw [coordinateTriangleTurningIntegral_reindex D G c s hG hGi hc R R' (by decide),
    coordinateTriangleTurningIntegral_reindex D F b r hF hFi hb Q Q' (by decide)] at heq
  simp only [r, s, triangleSidePermutation_orientation, triangleSidePermutation_symm_zero,
    triangleSidePermutation_symm_two, one_mul] at heq
  rw [coordinateTriangleTurningIntegral_swap D G c hG hGi hc R (side_successor_ne j),
    coordinateTriangleTurningIntegral_swap D F b hF hFi hb Q (side_successor_ne i)] at heq
  linarith

end PoincareConjecture.Topology.Surface
