import PoincareConjecture.Proofs.M13.SpacetimeSlices
import PoincareConjecture.Proofs.M13.ConnectionScale
import PoincareConjecture.Definitions.M12HorizontalCalculus








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  {F : GeneralizedFlowSpacetime n X time I}

namespace SliceData

variable {U W : Set F.Point}

noncomputable def transportLeviCivita (B : SliceData F U) (h : U = W)
    (D : LeviCivitaData B.metricOnPoints) :
    LeviCivitaData (B.transport h).metricOnPoints := by
  subst W
  exact D

noncomputable def derivativeValue (B : SliceData F U)
    (D : LeviCivitaData B.metricOnPoints) (V : HorizontalSection F)
    (x : B.Point) (v : SpacetimeModelVector n) : SpacetimeModelVector n :=
  (B.tangentEquiv x
    (D.connection (fun y ↦ (B.tangentEquiv y).symm (V y.val)) x
      ((B.tangentEquiv x).symm (F.horizontalProjection x.val v)))).val

theorem transport_derivativeValue (B : SliceData F U) (h : U = W)
    (D : LeviCivitaData B.metricOnPoints) (V : HorizontalSection F)
    (x : B.Point) (v : SpacetimeModelVector n) :
    (B.transport h).derivativeValue (B.transportLeviCivita h D) V
      (B.identification h x) v = B.derivativeValue D V x v := by
  subst W
  rfl

end SliceData

variable {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

theorem rawLeafwise_derivative_val_at (D : LeafwiseLeviCivitaFamily F S)
    (V : HorizontalSection F) (t : ℝ) (x : (S t).Point)
    (v : SpacetimeModelVector n) :
    (rawLeafwiseCovariantDerivative D V x.val (F.horizontalProjection x.val v)).val =
      ((S t).tangentEquiv x
        ((D.sliceConnection t).connection (restrictHorizontalSection S t V) x
          (((S t).tangentEquiv x).symm (F.horizontalProjection x.val v)))).val := by
  rcases x with ⟨p, hp⟩
  subst t
  rfl

theorem rescaledSliceData_derivativeValue
    (F : GeneralizedFlowSpacetime n X time I) {t : ℝ}
    (G : SpacetimeSliceGeometry F t) (D : LeviCivitaData G.metricOnPoints)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (V : HorizontalSection F)
    (x : G.Point) (v : SpacetimeModelVector n) :
    (rescaledSliceData F G Q hQ a).derivativeValue (scaleLeviCivitaData D Q hQ)
      (fun p ↦ parabolicSpacetimeHorizontal F Q hQ a p (V p)) x v =
      (G.tangentEquiv x
        (D.connection (fun y ↦ (G.tangentEquiv y).symm (V y.val)) x
          ((G.tangentEquiv x).symm (F.horizontalProjection x.val v)))).val := by
  change (parabolicSpacetimeHorizontal F Q hQ a x.val
    (G.tangentEquiv x
      (D.connection
        (fun y ↦ (G.tangentEquiv y).symm
          ((parabolicSpacetimeHorizontal F Q hQ a y.val).symm
            (parabolicSpacetimeHorizontal F Q hQ a y.val (V y.val)))) x
        ((G.tangentEquiv x).symm
          ((parabolicSpacetimeHorizontal F Q hQ a x.val).symm
            ((parabolicSpacetime F Q hQ a).horizontalProjection x.val v)))))).val = _
  rw [parabolicSpacetime_projection]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rfl

noncomputable def parabolicLeafwiseConnection
    (D : LeafwiseLeviCivitaFamily F S) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    LeafwiseLeviCivitaFamily (parabolicSpacetime F Q hQ a)
      (parabolicSpacetimeSlice F S Q hQ a) where
  sliceConnection s :=
    (rescaledSliceData F (S (parabolicTimeInv Q a s)) Q hQ a).transportLeviCivita
      (parabolicSliceSet_eq F Q hQ a s)
      (scaleLeviCivitaData (D.sliceConnection (parabolicTimeInv Q a s)) Q hQ)

theorem parabolic_leafwise_projection_val
    (D : LeafwiseLeviCivitaFamily F S) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (V : HorizontalSection F) (p : F.Point) (v : SpacetimeModelVector n) :
    (rawLeafwiseCovariantDerivative (parabolicLeafwiseConnection D Q hQ a)
      (fun q ↦ parabolicSpacetimeHorizontal F Q hQ a q (V q)) p
      ((parabolicSpacetime F Q hQ a).horizontalProjection p v)).val =
        (rawLeafwiseCovariantDerivative D V p (F.horizontalProjection p v)).val := by
  let s := parabolicTime Q a (F.timeFunction p)
  let t := parabolicTimeInv Q a s
  let x : (S t).Point :=
    ⟨p, (parabolicTimeInv_parabolicTime Q hQ a (F.timeFunction p)).symm⟩
  let B := rescaledSliceData F (S t) Q hQ a
  let h := parabolicSliceSet_eq F Q hQ a s
  let y : (parabolicSpacetimeSlice F S Q hQ a s).Point := B.identification h x
  have hy : y.val = p := SliceData.identification_val B h x
  have htarget := rawLeafwise_derivative_val_at (parabolicLeafwiseConnection D Q hQ a)
    (fun q ↦ parabolicSpacetimeHorizontal F Q hQ a q (V q)) s y v
  have htransport := SliceData.transport_derivativeValue B h
    (scaleLeviCivitaData (D.sliceConnection t) Q hQ)
    (fun q ↦ parabolicSpacetimeHorizontal F Q hQ a q (V q)) x v
  have hscale := rescaledSliceData_derivativeValue F (S t) (D.sliceConnection t)
    Q hQ a V x v
  have hsource := rawLeafwise_derivative_val_at D V t x v
  have hvalue := htarget.trans (htransport.trans (hscale.trans hsource.symm))
  have hpoint := congrArg
    (fun q : (parabolicSpacetime F Q hQ a).Point ↦
      (rawLeafwiseCovariantDerivative (parabolicLeafwiseConnection D Q hQ a)
        (fun z ↦ parabolicSpacetimeHorizontal F Q hQ a z (V z)) q
        ((parabolicSpacetime F Q hQ a).horizontalProjection q v)).val) hy
  exact hpoint.symm.trans hvalue

theorem parabolic_leafwise_chosen
    (D : LeafwiseLeviCivitaFamily F S) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (V : HorizontalSection F) (p : F.Point) (v : F.Horizontal p) :
    rawLeafwiseCovariantDerivative (parabolicLeafwiseConnection D Q hQ a)
      (fun q ↦ parabolicSpacetimeHorizontal F Q hQ a q (V q)) p
      (parabolicSpacetimeHorizontal F Q hQ a p v) =
        parabolicSpacetimeHorizontal F Q hQ a p (rawLeafwiseCovariantDerivative D V p v) := by
  apply Subtype.ext
  have h := parabolic_leafwise_projection_val D Q hQ a V p v.val
  rw [parabolicSpacetime_projection, F.horizontalProjection_identity] at h
  exact h

end PoincareConjecture.M13
