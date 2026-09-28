import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Restriction
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.LieTensor











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

local notation "H% " V => (fun q : F.Point ↦ TotalSpace.mk'
  (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) q (V q))

theorem rawLeafwiseCovariantDerivative_add
    (D : LeafwiseLeviCivitaFamily F S) {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p) :
    rawLeafwiseCovariantDerivative D (V + W) p =
      rawLeafwiseCovariantDerivative D V p + rawLeafwiseCovariantDerivative D W p := by
  let t := F.timeFunction p
  let x := spacetimeSlicePoint S p
  have hv := (S t).restrictHorizontalSection_differentiableAt V x hV
  have hw := (S t).restrictHorizontalSection_differentiableAt W x hW
  have hr : restrictHorizontalSection S t (V + W) =
      restrictHorizontalSection S t V + restrictHorizontalSection S t W := by
    funext y
    exact map_add ((S t).tangentEquiv y).symm _ _
  let j := (S t).tangentEquiv x
  apply ContinuousLinearMap.ext
  intro v
  change j ((D.sliceConnection t).connection (restrictHorizontalSection S t (V + W)) x
    (j.symm v)) = j ((D.sliceConnection t).connection (restrictHorizontalSection S t V) x
    (j.symm v)) + j ((D.sliceConnection t).connection (restrictHorizontalSection S t W) x
    (j.symm v))
  erw [hr, (D.sliceConnection t).connection.isCovariantDerivativeOn.add hv hw]
  simp only [add_apply, map_add]
  rfl

theorem rawLeafwiseCovariantDerivative_smul
    (D : LeafwiseLeviCivitaFamily F S) {V : HorizontalSection F}
    {f : F.Point → ℝ} {p : F.Point}
    (hf : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) f p)
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (v : F.Horizontal p) :
    rawLeafwiseCovariantDerivative D (f • V) p v =
      f p • rawLeafwiseCovariantDerivative D V p v +
        mvfderiv (spacetimeModel n) f p v.val • V p := by
  let t := F.timeFunction p
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
  let x := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  have hv := (S t).restrictHorizontalSection_differentiableAt V x hV
  have hi := ((S t).inclusion_smooth x).mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ)
      (f ∘ (Subtype.val : (S t).Point → F.Point)) x := hf.comp x hi
  have hr : restrictHorizontalSection S t (f • V) =
      (f ∘ (Subtype.val : (S t).Point → F.Point)) • restrictHorizontalSection S t V := by
    funext y
    exact map_smul ((S t).tangentEquiv y).symm _ _
  have hd : mvfderiv (𝓡 n) (f ∘ (Subtype.val : (S t).Point → F.Point)) x (j.symm v) =
      mvfderiv (spacetimeModel n) f p v.val := by
    rw [mvfderiv_comp_apply x hf hi, ← (S t).tangentEquiv_eq]
    simp only [j, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  change j ((D.sliceConnection t).connection (restrictHorizontalSection S t (f • V)) x
    (j.symm v)) = _
  erw [hr, (D.sliceConnection t).connection.isCovariantDerivativeOn.leibniz hv hf']
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, hd]
  simp only [j, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem rawHorizontalCovariantDerivative_isCovariantDerivative
    (D : LeafwiseLeviCivitaFamily F S) :
    IsCovariantDerivativeOn (I := spacetimeModel n) (EuclideanSpace ℝ (Fin n))
      (rawHorizontalCovariantDerivative D) univ where
  add hV hW _ := by
    apply ContinuousLinearMap.ext
    intro Z
    simp only [rawHorizontalCovariantDerivative, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      rawLeafwiseCovariantDerivative_add D hV hW, horizontalTimeBracket_add hV hW,
      smul_add]
    abel
  leibniz := by
    intro V f p hV hf _
    apply ContinuousLinearMap.ext
    intro Z
    simp only [rawHorizontalCovariantDerivative, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, rawLeafwiseCovariantDerivative_smul D hf hV,
      horizontalTimeBracket_smul hf hV, smul_add, smul_smul]
    have hd := congrArg (mvfderiv (spacetimeModel n) f p) (F.tangent_decomposition p Z)
    simp only [map_add, map_smul, smul_eq_mul] at hd
    rw [hd]
    simp only [GeneralizedFlowSpacetime.timeFunction]
    module


noncomputable def rawHorizontalConnection (D : LeafwiseLeviCivitaFamily F S) :
    CovariantDerivative (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) F.Horizontal :=
  ⟨rawHorizontalCovariantDerivative D, rawHorizontalCovariantDerivative_isCovariantDerivative D⟩

theorem rawHorizontalCovariantDerivative_time
    (D : LeafwiseLeviCivitaFamily F S) (V : HorizontalSection F) (p : F.Point) :
    rawHorizontalCovariantDerivative D V p (F.timeVector p) =
      horizontalTimeBracket F V p := by
  have hp : F.horizontalProjection p (F.timeVector p) = 0 := by
    apply Subtype.ext
    simp only [F.horizontalProjection_eq, F.timeVector_normalized, one_smul, sub_self]
    rfl
  change rawLeafwiseCovariantDerivative D V p (F.horizontalProjection p (F.timeVector p)) +
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p (F.timeVector p)) •
      horizontalTimeBracket F V p = _
  erw [hp, map_zero, F.timeVector_normalized, one_smul, zero_add]

theorem rawHorizontalCovariantDerivative_horizontal
    (D : LeafwiseLeviCivitaFamily F S) (V : HorizontalSection F) (p : F.Point)
    (v : F.Horizontal p) :
    rawHorizontalCovariantDerivative D V p v.val =
      rawLeafwiseCovariantDerivative D V p v := by
  change rawLeafwiseCovariantDerivative D V p (F.horizontalProjection p v.val) +
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p v.val) •
      horizontalTimeBracket F V p = _
  erw [F.horizontalProjection_identity, v.property, zero_smul, add_zero]

theorem rawLeafwiseCovariantDerivative_metric
    (D : LeafwiseLeviCivitaFamily F S) {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p)
    (v : F.Horizontal p) :
    mvfderiv (spacetimeModel n) (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p v.val =
      F.horizontalMetric.inner p (rawLeafwiseCovariantDerivative D V p v) (W p) +
        F.horizontalMetric.inner p (V p) (rawLeafwiseCovariantDerivative D W p v) := by
  let t := F.timeFunction p
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
  let x := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  let : RiemannianBundle (TangentSpace (𝓡 n) : (S t).Point → Type _) :=
    ⟨(S t).metricOnPoints.toRiemannianMetric⟩
  have hv := (S t).restrictHorizontalSection_differentiableAt V x hV
  have hw := (S t).restrictHorizontalSection_differentiableAt W x hW
  have hm := (D.sliceConnection t).metricCompatible.mvfderiv_inner_eq
    (x := x) (fun _ ↦ j.symm v) hv hw
  change mvfderiv (𝓡 n) (fun y : (S t).Point ↦ (S t).metricOnPoints.inner y
      (restrictHorizontalSection S t V y) (restrictHorizontalSection S t W y)) x
      (j.symm v) =
    (S t).metricOnPoints.inner x
        ((D.sliceConnection t).connection (restrictHorizontalSection S t V) x (j.symm v))
        (restrictHorizontalSection S t W x) +
      (S t).metricOnPoints.inner x (restrictHorizontalSection S t V x)
        ((D.sliceConnection t).connection (restrictHorizontalSection S t W) x (j.symm v)) at hm
  have he : (fun y : (S t).Point ↦ (S t).metricOnPoints.inner y
      (restrictHorizontalSection S t V y) (restrictHorizontalSection S t W y)) =
      (fun q : F.Point ↦ F.horizontalMetric.inner q (V q) (W q)) ∘ Subtype.val := by
    funext y
    exact ((S t).metric_eq y _ _).trans (by
      simp only [restrictHorizontalSection, ContinuousLinearEquiv.apply_symm_apply]
      rfl)
  have hg := (F.horizontalMetric.contMDiff p).mdifferentiableAt (by simp)
  have hh := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : F.Point ↦ ℝ) hV hW
  rw [mdifferentiableAt_totalSpace] at hh
  have hpair : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ)
      (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p := hh.2
  have hi := ((S t).inclusion_smooth x).mdifferentiableAt (by simp)
  erw [he, mvfderiv_comp_apply x hpair hi, ← (S t).tangentEquiv_eq] at hm
  simp only [j, ContinuousLinearEquiv.apply_symm_apply] at hm
  erw [(S t).metric_eq, (S t).metric_eq] at hm
  simpa only [restrictHorizontalSection, rawLeafwiseCovariantDerivative,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply] using! hm

theorem rawHorizontalCovariantDerivative_metric_defect
    (D : LeafwiseLeviCivitaFamily F S) {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p)
    (Z : TangentSpace (spacetimeModel n) p) :
    mvfderiv (spacetimeModel n) (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p Z -
      F.horizontalMetric.inner p (rawHorizontalCovariantDerivative D V p Z) (W p) -
      F.horizontalMetric.inner p (V p) (rawHorizontalCovariantDerivative D W p Z) =
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p Z) *
      horizontalMetricLieDerivative F p (V p) (W p) := by
  have hd := congrArg
    (mvfderiv (spacetimeModel n) (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p)
    (F.tangent_decomposition p Z)
  simp only [map_add, map_smul, smul_eq_mul,
    rawLeafwiseCovariantDerivative_metric D hV hW] at hd
  rw [horizontalMetricLieDerivative_on_differentiable_fields hV hW]
  simp only [rawHorizontalCovariantDerivative, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_apply, smul_eq_mul,
    horizontalMetricLieDerivativeOnFields]
  rw [hd]
  simp only [GeneralizedFlowSpacetime.timeFunction]
  ring!

end PoincareConjecture
