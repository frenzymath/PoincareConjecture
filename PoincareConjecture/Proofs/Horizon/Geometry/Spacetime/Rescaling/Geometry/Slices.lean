import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Geometry.Base
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Geometry.SliceData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

noncomputable def rescaledSliceData (S : GeneralizedFlowSpacetime n X time I)
    {t : ℝ} (D : SpacetimeSliceGeometry S t) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    SliceData (parabolicSpacetime S Q hQ a) {p | S.timeFunction p = t} := by
  let g := scaleSmoothMetric D.metricOnPoints Q hQ
  refine {
    chartedSpace := D.chartedSpace
    isManifold := D.isManifold
    t3Space := D.t3Space
    secondCountable := D.secondCountable
    measurableSpace := D.measurableSpace
    borelSpace := D.borelSpace
    inclusion_smooth := D.inclusion_smooth
    inclusion_embedding := D.inclusion_embedding
    inclusion_differential_injective := D.inclusion_differential_injective
    tangentEquiv := fun x ↦ (D.tangentEquiv x).trans
      (parabolicSpacetimeHorizontal S Q hQ a x.val)
    tangentEquiv_eq := ?_
    metric := g
    metric_eq := ?_ }
  · intro x v
    exact D.tangentEquiv_eq x v
  · intro x v w
    change Q * D.metricOnPoints.inner x v w =
      (parabolicSpacetime S Q hQ a).horizontalMetric.inner x.val
        (parabolicSpacetimeHorizontal S Q hQ a x.val (D.tangentEquiv x v))
        (parabolicSpacetimeHorizontal S Q hQ a x.val (D.tangentEquiv x w))
    rw [parabolicSpacetime_metric]
    exact congrArg (Q * ·) (D.metric_eq x v w)

theorem parabolicSliceSet_eq (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    {p : X | S.timeFunction p = parabolicTimeInv Q a s} =
      {p : X | (parabolicSpacetime S Q hQ a).timeFunction p = s} := by
  ext p
  change S.timeFunction p = parabolicTimeInv Q a s ↔
    parabolicTime Q a (S.timeFunction p) = s
  constructor
  · intro hp
    rw [hp]
    exact parabolicTime_parabolicTimeInv Q hQ a s
  · intro hp
    have h := congrArg (parabolicTimeInv Q a) hp
    simpa only [parabolicTimeInv_parabolicTime Q hQ a] using h

noncomputable def parabolicSpacetimeSlice (S : GeneralizedFlowSpacetime n X time I)
    (D : ∀ t, SpacetimeSliceGeometry S t) (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    SpacetimeSliceGeometry (parabolicSpacetime S Q hQ a) s :=
  ((rescaledSliceData S (D (parabolicTimeInv Q a s)) Q hQ a).transport
    (parabolicSliceSet_eq S Q hQ a s)).toSliceGeometry

noncomputable def parabolicSliceIdentificationInv
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    Diffeomorph (𝓡 n) (𝓡 n) (D (parabolicTimeInv Q a s)).Point
      (parabolicSpacetimeSlice S D Q hQ a s).Point ∞ :=
  (rescaledSliceData S (D (parabolicTimeInv Q a s)) Q hQ a).identification
    (parabolicSliceSet_eq S Q hQ a s)

theorem parabolicSliceIdentificationInv_val
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) (x : (D (parabolicTimeInv Q a s)).Point) :
    (parabolicSliceIdentificationInv S D Q hQ a s x).val = x.val :=
  SliceData.identification_val (rescaledSliceData S (D (parabolicTimeInv Q a s)) Q hQ a)
    (parabolicSliceSet_eq S Q hQ a s) x

theorem parabolicSliceIdentificationInv_tangent
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) (x : (D (parabolicTimeInv Q a s)).Point)
    (v : TangentSpace (𝓡 n) x) :
    (show SpacetimeModelVector n from
      ((parabolicSpacetimeSlice S D Q hQ a s).tangentEquiv
        (parabolicSliceIdentificationInv S D Q hQ a s x)
        (mfderiv (𝓡 n) (𝓡 n) (parabolicSliceIdentificationInv S D Q hQ a s) x v)).val) =
      ((D (parabolicTimeInv Q a s)).tangentEquiv x v).val :=
  SliceData.identification_tangent (rescaledSliceData S (D (parabolicTimeInv Q a s)) Q hQ a)
    (parabolicSliceSet_eq S Q hQ a s) x v

theorem parabolicSliceIdentificationInv_metric
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) (x : (D (parabolicTimeInv Q a s)).Point)
    (v w : TangentSpace (𝓡 n) x) :
    (parabolicSpacetimeSlice S D Q hQ a s).metricOnPoints.inner
      (parabolicSliceIdentificationInv S D Q hQ a s x)
      (mfderiv (𝓡 n) (𝓡 n) (parabolicSliceIdentificationInv S D Q hQ a s) x v)
      (mfderiv (𝓡 n) (𝓡 n) (parabolicSliceIdentificationInv S D Q hQ a s) x w) =
        Q * (D (parabolicTimeInv Q a s)).metricOnPoints.inner x v w :=
  SliceData.identification_metric (rescaledSliceData S (D (parabolicTimeInv Q a s)) Q hQ a)
    (parabolicSliceSet_eq S Q hQ a s) x v w

noncomputable def parabolicSliceIdentification
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    Diffeomorph (𝓡 n) (𝓡 n) (D t).Point
      (parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).Point ∞ :=
  (sliceTimeIdentification D (parabolicTimeInv_parabolicTime Q hQ a t).symm).trans
    (parabolicSliceIdentificationInv S D Q hQ a (parabolicTime Q a t))

theorem parabolicSliceIdentification_val
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) (x : (D t).Point) :
    (parabolicSliceIdentification S D Q hQ a t x).val = x.val := by
  exact (parabolicSliceIdentificationInv_val S D Q hQ a (parabolicTime Q a t) _).trans
    (sliceTimeIdentification_val D _ x)

theorem parabolicSliceIdentification_tangent
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) (x : (D t).Point)
    (v : TangentSpace (𝓡 n) x) :
    (show SpacetimeModelVector n from
      ((parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).tangentEquiv
        (parabolicSliceIdentification S D Q hQ a t x)
        (mfderiv (𝓡 n) (𝓡 n) (parabolicSliceIdentification S D Q hQ a t) x v)).val) =
      (parabolicSpacetimeHorizontal S Q hQ a x.val ((D t).tangentEquiv x v)).val := by
  let f := sliceTimeIdentification D (parabolicTimeInv_parabolicTime Q hQ a t).symm
  let g := parabolicSliceIdentificationInv S D Q hQ a (parabolicTime Q a t)
  change ((parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).tangentEquiv
    (g (f x)) (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x v)).val = _
  rw [mfderiv_comp x (g.mdifferentiable (by simp) _) (f.mdifferentiable (by simp) _)]
  exact (parabolicSliceIdentificationInv_tangent S D Q hQ a (parabolicTime Q a t)
    (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)).trans
      (sliceTimeIdentification_tangent D _ x v)

theorem parabolicSliceIdentification_metric
    (S : GeneralizedFlowSpacetime n X time I) (D : ∀ t, SpacetimeSliceGeometry S t)
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    MetricHomothety (D t).metricOnPoints
      (parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).metricOnPoints
      (parabolicSliceIdentification S D Q hQ a t) Q := by
  intro x v w
  let f := sliceTimeIdentification D (parabolicTimeInv_parabolicTime Q hQ a t).symm
  let g := parabolicSliceIdentificationInv S D Q hQ a (parabolicTime Q a t)
  change (parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).metricOnPoints.inner
    (g (f x)) (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x v)
    (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x w) = _
  rw [mfderiv_comp x (g.mdifferentiable (by simp) _) (f.mdifferentiable (by simp) _)]
  exact (parabolicSliceIdentificationInv_metric S D Q hQ a (parabolicTime Q a t) (f x)
    (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)).trans
      (congrArg (Q * ·) (sliceTimeIdentification_metric D _ x v w))

end PoincareConjecture.ParabolicRescaling
