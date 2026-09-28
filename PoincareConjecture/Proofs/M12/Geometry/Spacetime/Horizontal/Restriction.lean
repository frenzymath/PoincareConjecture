import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Choice
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.MetricDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}

namespace SpacetimeSliceGeometry

variable {t : ℝ} (S : SpacetimeSliceGeometry F t)

private theorem tangentEquiv_coordinates_smooth (x : S.Point) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun y : S.Point ↦ ContinuousLinearMap.inCoordinates
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : S.Point → Type _)
        (EuclideanSpace ℝ (Fin n)) F.Horizontal
        x y x.val y.val (S.tangentEquiv y).toContinuousLinearMap) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : S.Point → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y : S.Point ↦ TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hfield := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞) hx).clm_bundle_apply hv
  have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞ (Subtype.val : S.Point → F.Point) :=
    S.inclusion_smooth
  have hderiv := ((hi x).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
    hfield (hi x)
  have hproj : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, E)) ∞
      (fun v : TangentBundle (spacetimeModel n) F.Point ↦
        TotalSpace.mk' E (E := F.Horizontal) v.proj (F.horizontalProjection v.proj v.2)) :=
    F.horizontalProjection_smooth
  have h := (hproj _).comp x hderiv
  rw [contMDiffAt_totalSpace] at h
  apply h.2.congr_of_eventuallyEq
  filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
    ((trivializationAt E F.Horizontal x.val).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E F.Horizontal x.val))] with y hy
  dsimp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  congr 2
  apply congrArg (fun w : F.Horizontal y.val ↦ TotalSpace.mk' E y.val w)
  have ht : (S.tangentEquiv y ((e.symmL ℝ y) v)).val =
      mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : S.Point → F.Point) y
        ((e.symmL ℝ y) v) := S.tangentEquiv_eq _ _
  change S.tangentEquiv y ((e.symmL ℝ y) v) = _
  exact (F.horizontalProjection_identity y.val _).symm.trans
    (congrArg (F.horizontalProjection y.val) ht)

private theorem tangentEquiv_coordinates_invertible (x : S.Point) :
    (ContinuousLinearMap.inCoordinates
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : S.Point → Type _)
      (EuclideanSpace ℝ (Fin n)) F.Horizontal
      x x x.val x.val (S.tangentEquiv x).toContinuousLinearMap).IsInvertible := by
  rw [ContinuousLinearMap.inCoordinates_eq
    (FiberBundle.mem_baseSet_trivializationAt _ _ _)
    (FiberBundle.mem_baseSet_trivializationAt _ _ _)]
  exact ContinuousLinearMap.isInvertible_equiv.comp
    (ContinuousLinearMap.isInvertible_equiv.comp ContinuousLinearMap.isInvertible_equiv)

private theorem tangentEquiv_symm_coordinates_smooth (x : S.Point) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun y : S.Point ↦ ContinuousLinearMap.inCoordinates
        (EuclideanSpace ℝ (Fin n)) F.Horizontal
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : S.Point → Type _)
        x.val y.val x y (S.tangentEquiv y).symm.toContinuousLinearMap) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  have h := (S.tangentEquiv_coordinates_invertible x).contDiffAt_map_inverse.contMDiffAt.comp x
    (S.tangentEquiv_coordinates_smooth x)
  apply h.congr_of_eventuallyEq
  have hi : Continuous (Subtype.val : S.Point → F.Point) := S.inclusion_smooth.continuous
  filter_upwards [(trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : S.Point → Type _) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt _ _ _),
    hi.continuousAt.preimage_mem_nhds
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) F.Horizontal x.val).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt _ _ _))] with y hy hy'
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy',
    ContinuousLinearMap.inCoordinates_eq hy' hy]
  simp only [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

theorem restrictHorizontalSection_smoothAt
    (V : HorizontalSection F) (x : S.Point)
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : F.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := F.Horizontal) q (V q)) x.val) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y : S.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : S.Point → Type _)) y
        ((S.tangentEquiv y).symm (V y.val))) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞ (Subtype.val : S.Point → F.Point) :=
    S.inclusion_smooth
  exact (S.tangentEquiv_symm_coordinates_smooth x).clm_apply_of_inCoordinates
    (b₁ := (Subtype.val : S.Point → F.Point)) (b₂ := id)
    (hV.comp x (hi x)) contMDiffAt_id

theorem restrictHorizontalSection_differentiableAt
    (V : HorizontalSection F) (x : S.Point)
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun q : F.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := F.Horizontal) q (V q)) x.val) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y : S.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : S.Point → Type _)) y
        ((S.tangentEquiv y).symm (V y.val))) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞ (Subtype.val : S.Point → F.Point) :=
    S.inclusion_smooth
  have hc := (S.tangentEquiv_symm_coordinates_smooth x).mdifferentiableAt (by simp)
  exact hc.clm_apply_of_inCoordinates (b₁ := (Subtype.val : S.Point → F.Point)) (b₂ := id)
    (hV.comp x ((hi x).mdifferentiableAt (by simp))) mdifferentiableAt_id

end SpacetimeSliceGeometry

variable {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

theorem restrictHorizontalSection_smooth
    {U : Set F.Point} (hU : IsOpen U) {V : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U) (t : ℝ) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (restrictHorizontalSection S t V)) (Subtype.val ⁻¹' U) := by
  intro x hx
  exact ((S t).restrictHorizontalSection_smoothAt V x
    (hV.contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

namespace LeafwiseLeviCivitaFamily

theorem rawLeafwiseCovariantDerivative_eq
    (D D' : LeafwiseLeviCivitaFamily F S) {V : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun q : F.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := F.Horizontal) q (V q)) p) :
    rawLeafwiseCovariantDerivative D V p = rawLeafwiseCovariantDerivative D' V p := by
  have hv := (S (F.timeFunction p)).restrictHorizontalSection_differentiableAt V
    (spacetimeSlicePoint S p) hV
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg ((S (F.timeFunction p)).tangentEquiv (spacetimeSlicePoint S p))
    ((D.sliceConnection (F.timeFunction p)).connection_eq_of_mdifferentiableAt
      (D'.sliceConnection (F.timeFunction p)) hv
        (((S (F.timeFunction p)).tangentEquiv (spacetimeSlicePoint S p)).symm v))

theorem rawHorizontalCovariantDerivative_eq
    (D D' : LeafwiseLeviCivitaFamily F S) {V : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun q : F.Point ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := F.Horizontal) q (V q)) p) :
    rawHorizontalCovariantDerivative D V p = rawHorizontalCovariantDerivative D' V p := by
  unfold rawHorizontalCovariantDerivative
  rw [D.rawLeafwiseCovariantDerivative_eq D' hV]

end LeafwiseLeviCivitaFamily

end PoincareConjecture
