import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Geometry.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Horizontal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem parabolic_slice_calculus (t : ℝ) :
    MetricHomothetyCalculus (R.slices t).metricOnPoints
      ((spacetimeRescaling R Q hQ a).realization.slices (parabolicTime Q a t)).metricOnPoints
      ((spacetimeRescaling R Q hQ a).sliceIdentification t) Q :=
  metricHomothetyCalculus _ _ _ Q hQ ((spacetimeRescaling R Q hQ a).slice_metric t)

theorem parabolic_slicePoint (p : R.spacetime.Point) :
    (spacetimeRescaling R Q hQ a).sliceIdentification (R.spacetime.timeFunction p)
      (spacetimeSlicePoint R.slices p) =
        spacetimeSlicePoint (spacetimeRescaling R Q hQ a).realization.slices p := by
  apply Subtype.ext
  exact (spacetimeRescaling R Q hQ a).sliceIdentification_eq _ _

theorem parabolic_slice_tangent (p : R.spacetime.Point) (v : R.spacetime.Horizontal p) :
    mfderiv (𝓡 n) (𝓡 n)
      ((spacetimeRescaling R Q hQ a).sliceIdentification (R.spacetime.timeFunction p))
      (spacetimeSlicePoint R.slices p)
      (((R.slices (R.spacetime.timeFunction p)).tangentEquiv
        (spacetimeSlicePoint R.slices p)).symm v) =
      (((spacetimeRescaling R Q hQ a).realization.slices
        ((spacetimeRescaling R Q hQ a).realization.spacetime.timeFunction p)).tangentEquiv
        (spacetimeSlicePoint (spacetimeRescaling R Q hQ a).realization.slices p)).symm
          ((spacetimeRescaling R Q hQ a).horizontal p v) := by
  let P := spacetimeRescaling R Q hQ a
  apply ((P.realization.slices (P.realization.spacetime.timeFunction p)).tangentEquiv
    (spacetimeSlicePoint P.realization.slices p)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have h := P.slice_tangent (R.spacetime.timeFunction p) (spacetimeSlicePoint R.slices p)
    (((R.slices (R.spacetime.timeFunction p)).tangentEquiv
      (spacetimeSlicePoint R.slices p)).symm v)
  rw [parabolic_slicePoint] at h
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

variable (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
  (D' : LeafwiseLeviCivitaFamily (spacetimeRescaling R Q hQ a).realization.spacetime
    (spacetimeRescaling R Q hQ a).realization.slices)

theorem parabolic_horizontal_riemann (p : R.spacetime.Point)
    (v w z q : R.spacetime.Horizontal p) :
    horizontalRiemann D' p ((spacetimeRescaling R Q hQ a).horizontal p v)
      ((spacetimeRescaling R Q hQ a).horizontal p w)
      ((spacetimeRescaling R Q hQ a).horizontal p z)
      ((spacetimeRescaling R Q hQ a).horizontal p q) = Q * horizontalRiemann D p v w z q := by
  let x := spacetimeSlicePoint R.slices p
  let j := (R.slices (R.spacetime.timeFunction p)).tangentEquiv x
  have h := (parabolic_slice_calculus (R := R) (Q := Q) (hQ := hQ) (a := a)
    (R.spacetime.timeFunction p)).riemann_eq (D.sliceConnection (R.spacetime.timeFunction p))
      (D'.sliceConnection (parabolicTime Q a (R.spacetime.timeFunction p))) x
      (j.symm v) (j.symm w) (j.symm z) (j.symm q)
  dsimp only [x, j] at h
  erw [parabolic_slicePoint, parabolic_slice_tangent (R := R) (Q := Q) (a := a) p v,
    parabolic_slice_tangent (R := R) (Q := Q) (a := a) p w,
    parabolic_slice_tangent (R := R) (Q := Q) (a := a) p z,
    parabolic_slice_tangent (R := R) (Q := Q) (a := a) p q] at h
  exact h

theorem parabolic_horizontal_ricci (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p) :
    horizontalRicci D' p ((spacetimeRescaling R Q hQ a).horizontal p v)
      ((spacetimeRescaling R Q hQ a).horizontal p w) = horizontalRicci D p v w := by
  let x := spacetimeSlicePoint R.slices p
  let j := (R.slices (R.spacetime.timeFunction p)).tangentEquiv x
  have h := (parabolic_slice_calculus (R := R) (Q := Q) (hQ := hQ) (a := a)
    (R.spacetime.timeFunction p)).ricci_eq (D.sliceConnection (R.spacetime.timeFunction p))
      (D'.sliceConnection (parabolicTime Q a (R.spacetime.timeFunction p))) x (j.symm v) (j.symm w)
  dsimp only [x, j] at h
  erw [parabolic_slicePoint, parabolic_slice_tangent (R := R) (Q := Q) (a := a) p v,
    parabolic_slice_tangent (R := R) (Q := Q) (a := a) p w] at h
  exact h

theorem parabolic_horizontal_scalar (p : R.spacetime.Point) :
    horizontalScalarCurvature D' p = horizontalScalarCurvature D p / Q := by
  have h := (parabolic_slice_calculus (R := R) (Q := Q) (hQ := hQ) (a := a)
    (R.spacetime.timeFunction p)).scalar_eq (D.sliceConnection (R.spacetime.timeFunction p))
      (D'.sliceConnection (parabolicTime Q a (R.spacetime.timeFunction p)))
      (spacetimeSlicePoint R.slices p)
  rw [parabolic_slicePoint] at h
  exact h

theorem parabolic_horizontal_norm (p : R.spacetime.Point) :
    horizontalCurvatureNorm D' p = horizontalCurvatureNorm D p / Q := by
  have h := (parabolic_slice_calculus (R := R) (Q := Q) (hQ := hQ) (a := a)
    (R.spacetime.timeFunction p)).curvature_norm_eq (D.sliceConnection (R.spacetime.timeFunction p))
      (D'.sliceConnection (parabolicTime Q a (R.spacetime.timeFunction p)))
      (spacetimeSlicePoint R.slices p)
  rw [parabolic_slicePoint] at h
  exact h

theorem parabolic_horizontal_normSq (p : R.spacetime.Point) :
    horizontalCurvatureNormSq D' p = horizontalCurvatureNormSq D p / Q ^ 2 := by
  unfold horizontalCurvatureNormSq
  rw [parabolic_horizontal_norm D D', div_pow]

end PoincareConjecture.ParabolicRescaling
