import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Assembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

private theorem leafwise_eq_on_slice
    (D : LeafwiseLeviCivitaFamily F S) (V : HorizontalSection F)
    (p : F.Point) {t : ℝ} (ht : F.timeFunction p = t) (w : F.Horizontal p) :
    rawLeafwiseCovariantDerivative D V p w =
      (S t).tangentEquiv ⟨p, ht⟩
        ((D.sliceConnection t).connection (restrictHorizontalSection S t V) ⟨p, ht⟩
          (((S t).tangentEquiv ⟨p, ht⟩).symm w)) := by
  subst t
  rfl

theorem restrictHorizontalSection_leafwise
    (D : LeafwiseLeviCivitaFamily F S) (V W : HorizontalSection F) (t : ℝ) :
    restrictHorizontalSection S t (fun p => rawLeafwiseCovariantDerivative D W p (V p)) =
      fun x => (D.sliceConnection t).connection (restrictHorizontalSection S t W) x
        (restrictHorizontalSection S t V x) := by
  funext x
  change ((S t).tangentEquiv x).symm
    (rawLeafwiseCovariantDerivative D W x.val (V x.val)) = _
  rw [leafwise_eq_on_slice D W x.val x.property]
  exact (S t).tangentEquiv x |>.symm_apply_apply _

theorem horizontalRiemann_eq_leafwise_commutator
    (hMetric : M12MetricPredecessors.{u} n)
    (D : LeafwiseLeviCivitaFamily F S)
    {U : Set F.Point} (hU : IsOpen U) {V W Y Z : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U)
    (hW : IsSmoothHorizontalSectionOn F W U)
    (hZ : IsSmoothHorizontalSectionOn F Z U)
    {p : F.Point} (hp : p ∈ U) :
    horizontalRiemann D p (V p) (W p) (Y p) (Z p) =
      F.horizontalMetric.inner p
        (rawLeafwiseCovariantDerivative D
            (fun q => rawLeafwiseCovariantDerivative D Z q (W q)) p (V p) -
          rawLeafwiseCovariantDerivative D
            (fun q => rawLeafwiseCovariantDerivative D Z q (V q)) p (W p) -
          rawLeafwiseCovariantDerivative D Z p
            (rawLeafwiseCovariantDerivative D W p (V p) -
              rawLeafwiseCovariantDerivative D V p (W p))) (Y p) := by
  let t := F.timeFunction p
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
  let x := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  have hv := restrictHorizontalSection_smooth (S := S) hU hV t
  have hw := restrictHorizontalSection_smooth (S := S) hU hW t
  have hz := restrictHorizontalSection_smooth (S := S) hU hZ t
  have hopen : IsOpen ((Subtype.val : (S t).Point → F.Point) ⁻¹' U) :=
    hU.preimage (S t).inclusion_smooth.continuous
  have hxp : x ∈ (Subtype.val : (S t).Point → F.Point) ⁻¹' U := hp
  have hcurv := (hMetric.curvature_calculus (S t).Point (S t).metricOnPoints
    (D.sliceConnection t)).2.2.2.2 _ hopen _ _ _ hv hw hz x hxp
  have htors := (D.sliceConnection t).covariantDerivativeOnFields_sub_swap
    ((hv.contMDiffAt (hopen.mem_nhds hxp)).mdifferentiableAt (by simp))
    ((hw.contMDiffAt (hopen.mem_nhds hxp)).mdifferentiableAt (by simp))
  change (S t).metricOnPoints.inner x
      ((D.sliceConnection t).curvature x
        (restrictHorizontalSection S t V x) (restrictHorizontalSection S t W x)
        (restrictHorizontalSection S t Z x)) (j.symm (Y p)) = _
  rw [← hcurv, LeviCivitaData.curvatureOnFields, ← htors, (S t).metric_eq]
  have hd (A : HorizontalSection F) (a : F.Horizontal p) :
      rawLeafwiseCovariantDerivative D A p a =
        j ((D.sliceConnection t).connection (restrictHorizontalSection S t A) x
          (j.symm a)) := rfl
  rw [hd, hd, hd, hd, hd]
  rw [restrictHorizontalSection_leafwise D W Z t,
    restrictHorizontalSection_leafwise D V Z t]
  simp only [j, map_sub, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem horizontalRiemann_tensor
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T) :
    IsSmoothHorizontalCovariantTensor F (k := 4)
      (fun p v => horizontalRiemann D p (v 0) (v 1) (v 2) (v 3)) := by
  constructor
  · intro p
    let t := F.timeFunction p
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
    let x := spacetimeSlicePoint S p
    obtain ⟨A, hA⟩ := (hMetric.curvature_calculus (S t).Point (S t).metricOnPoints
      (D.sliceConnection t)).1.1 x
    refine ⟨A.compLinearMap (fun _ => ((S t).tangentEquiv x).symm.toLinearMap), ?_⟩
    exact fun v => hA (fun i => ((S t).tangentEquiv x).symm (v i))
  · intro U hU V hV
    have hd {W Z : HorizontalSection F}
        (hW : IsSmoothHorizontalSectionOn F W U)
        (hZ : IsSmoothHorizontalSectionOn F Z U) :=
      rawLeafwiseCovariantDerivative_apply_smooth hCoordinates D cover hU hW hZ
    have hR := ((hd (hV 0) (hd (hV 1) (hV 3))).sub_section
      (hd (hV 1) (hd (hV 0) (hV 3)))).sub_section
      (hd ((hd (hV 0) (hV 1)).sub_section (hd (hV 1) (hV 0))) (hV 3))
    intro p hp
    have h := (contMDiffAt_totalSpace.mp
      ((F.horizontalMetric.contMDiff p).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial F.Point ℝ)
        (hR.contMDiffAt (hU.mem_nhds hp))
        ((hV 2).contMDiffAt (hU.mem_nhds hp)))).2
    apply ContMDiffAt.contMDiffWithinAt
    apply h.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hp] with q hq
    exact horizontalRiemann_eq_leafwise_commutator hMetric D hU (hV 0) (hV 1) (hV 3) hq

end PoincareConjecture
