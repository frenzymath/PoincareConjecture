import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionSphereCharts










set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M74

variable {Y : GeneralizedSliceCarrier.{u}}

private noncomputable def sphereChartGlueMap (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace) (x : Y.carrier) :
    ThreeSphere := by
  classical
  exact if x ∈ e0.source then (standardSphereChart v).symm (e0 x)
    else (oppositeSphereChart v).symm (e1 x)

private noncomputable def sphereChartGlueInverse (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace) (x : ThreeSphere) :
    Y.carrier := by
  classical
  exact if x ∈ (standardSphereChart v).source then e0.symm (standardSphereChart v x)
    else e1.symm (oppositeSphereChart v x)

private theorem sphereChartGlueMap_first (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace) {x : Y.carrier}
    (hx : x ∈ e0.source) :
    sphereChartGlueMap v e0 e1 x = (standardSphereChart v).symm (e0 x) := by
  simp only [sphereChartGlueMap, if_pos hx]

private theorem sphereChartGlueInverse_first (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace) {x : ThreeSphere}
    (hx : x ∈ (standardSphereChart v).source) :
    sphereChartGlueInverse v e0 e1 x = e0.symm (standardSphereChart v x) := by
  simp only [sphereChartGlueInverse, if_pos hx]

private theorem sphereChartGlueMap_second (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace)
    (hover : ∀ x ∈ e0.source, x ∈ e1.source ↔ e0 x ≠ 0)
    (htransition : ∀ x ∈ e0.source, x ∈ e1.source →
      e1 x = EuclideanGeometry.inversion 0 2 (e0 x))
    {x : Y.carrier} (hx : x ∈ e1.source) :
    sphereChartGlueMap v e0 e1 x = (oppositeSphereChart v).symm (e1 x) := by
  by_cases hx0 : x ∈ e0.source
  · rw [sphereChartGlueMap_first v e0 e1 hx0, htransition x hx0 hx]
    exact (oppositeSphereChart_symm_inversion v ((hover x hx0).mp hx)).symm
  · simp only [sphereChartGlueMap, if_neg hx0]

private theorem sphereChartGlueInverse_second (v : ThreeSphere)
    (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace)
    (ht0 : e0.target = univ)
    (hover : ∀ x ∈ e0.source, x ∈ e1.source ↔ e0 x ≠ 0)
    (htransition : ∀ x ∈ e0.source, x ∈ e1.source →
      e1 x = EuclideanGeometry.inversion 0 2 (e0 x))
    {x : ThreeSphere} (hx : x ∈ (oppositeSphereChart v).source) :
    sphereChartGlueInverse v e0 e1 x = e1.symm (oppositeSphereChart v x) := by
  by_cases hx0 : x ∈ (standardSphereChart v).source
  · rw [sphereChartGlueInverse_first v e0 e1 hx0]
    have hz : standardSphereChart v x ≠ 0 :=
      (standardSphereChart_mem_opposite_iff v hx0).mp hx
    have hzt : standardSphereChart v x ∈ e0.target := by rw [ht0]; trivial
    have hy0 := e0.map_target hzt
    have hy1 : e0.symm (standardSphereChart v x) ∈ e1.source := by
      apply (hover _ hy0).mpr
      rwa [e0.right_inv hzt]
    have heq : e1 (e0.symm (standardSphereChart v x)) = oppositeSphereChart v x := by
      rw [htransition _ hy0 hy1, e0.right_inv hzt]
      exact (oppositeSphereChart_transition v hx0 hx).symm
    have hleft := e1.left_inv hy1
    rw [heq] at hleft
    exact hleft.symm
  · simp only [sphereChartGlueInverse, if_neg hx0]




noncomputable def diffeomorphOfSphereCharts (Y : GeneralizedSliceCarrier.{u})
    (v : ThreeSphere) (e0 e1 : OpenPartialHomeomorph Y.carrier StandardCapSpace)
    (ht0 : e0.target = univ) (ht1 : e1.target = univ)
    (hcover : e0.source ∪ e1.source = univ)
    (hover : ∀ x ∈ e0.source, x ∈ e1.source ↔ e0 x ≠ 0)
    (htransition : ∀ x ∈ e0.source, x ∈ e1.source →
      e1 x = EuclideanGeometry.inversion 0 2 (e0 x))
    (hs0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e0 e0.source)
    (hs1 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e1 e1.source)
    (hi0 : ContMDiff (𝓡 3) (𝓡 3) ∞ e0.symm)
    (hi1 : ContMDiff (𝓡 3) (𝓡 3) ∞ e1.symm) :
    Diffeomorph (𝓡 3) (𝓡 3) Y.carrier ThreeSphere ∞ := by
  have hsecond {x : Y.carrier} (hx : x ∈ e1.source) :=
    sphereChartGlueMap_second v e0 e1 hover htransition hx
  have hsecond_inv {x : ThreeSphere} (hx : x ∈ (oppositeSphereChart v).source) :=
    sphereChartGlueInverse_second v e0 e1 ht0 hover htransition hx
  refine {
    toFun := sphereChartGlueMap v e0 e1
    invFun := sphereChartGlueInverse v e0 e1
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro x
    by_cases hx0 : x ∈ e0.source
    · have ht : e0 x ∈ (standardSphereChart v).target := by simp
      rw [sphereChartGlueMap_first v e0 e1 hx0,
        sphereChartGlueInverse_first v e0 e1 ((standardSphereChart v).map_target ht),
        (standardSphereChart v).right_inv ht, e0.left_inv hx0]
    · have hx1 : x ∈ e1.source := by
        have hc : x ∈ e0.source ∪ e1.source := by rw [hcover]; trivial
        exact hc.resolve_left hx0
      have ht : e1 x ∈ (oppositeSphereChart v).target := by simp
      rw [hsecond hx1, hsecond_inv ((oppositeSphereChart v).map_target ht),
        (oppositeSphereChart v).right_inv ht, e1.left_inv hx1]
  · intro x
    by_cases hx0 : x ∈ (standardSphereChart v).source
    · have ht : standardSphereChart v x ∈ e0.target := by rw [ht0]; trivial
      rw [sphereChartGlueInverse_first v e0 e1 hx0,
        sphereChartGlueMap_first v e0 e1 (e0.map_target ht),
        e0.right_inv ht, (standardSphereChart v).left_inv hx0]
    · have hx1 : x ∈ (oppositeSphereChart v).source := by
        have hc : x ∈ (standardSphereChart v).source ∪ (oppositeSphereChart v).source := by
          rw [sphereCharts_cover]; trivial
        exact hc.resolve_left hx0
      have ht : oppositeSphereChart v x ∈ e1.target := by rw [ht1]; trivial
      rw [hsecond_inv hx1, hsecond (e1.map_target ht),
        e1.right_inv ht, (oppositeSphereChart v).left_inv hx1]
  · intro x
    by_cases hx0 : x ∈ e0.source
    · have hlocal := (standardSphereChart_symm_contMDiff v).contMDiffAt.comp x
        (hs0.contMDiffAt (e0.open_source.mem_nhds hx0))
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [e0.open_source.mem_nhds hx0] with y hy
      exact sphereChartGlueMap_first v e0 e1 hy
    · have hx1 : x ∈ e1.source := by
        have hc : x ∈ e0.source ∪ e1.source := by rw [hcover]; trivial
        exact hc.resolve_left hx0
      have hlocal := (oppositeSphereChart_symm_contMDiff v).contMDiffAt.comp x
        (hs1.contMDiffAt (e1.open_source.mem_nhds hx1))
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [e1.open_source.mem_nhds hx1] with y hy
      exact hsecond hy
  · intro x
    by_cases hx0 : x ∈ (standardSphereChart v).source
    · have hlocal := hi0.contMDiffAt.comp x
        ((standardSphereChart_contMDiffOn v).contMDiffAt
          ((standardSphereChart v).open_source.mem_nhds hx0))
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(standardSphereChart v).open_source.mem_nhds hx0] with y hy
      exact sphereChartGlueInverse_first v e0 e1 hy
    · have hx1 : x ∈ (oppositeSphereChart v).source := by
        have hc : x ∈ (standardSphereChart v).source ∪ (oppositeSphereChart v).source := by
          rw [sphereCharts_cover]; trivial
        exact hc.resolve_left hx0
      have hlocal := hi1.contMDiffAt.comp x
        ((oppositeSphereChart_contMDiffOn v).contMDiffAt
          ((oppositeSphereChart v).open_source.mem_nhds hx1))
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(oppositeSphereChart v).open_source.mem_nhds hx1] with y hy
      exact hsecond_inv hy

end PoincareConjecture.M74
