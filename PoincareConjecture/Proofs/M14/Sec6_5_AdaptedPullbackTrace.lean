import PoincareConjecture.Proofs.M14.Sec6_5_HorizontalIndexTrace
import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedFrame
import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedScale










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)




theorem adaptedPullbackIndex_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (P : Fin n → ∀ s, G.Horizontal (R.curve s))
    (hP : ∀ i, IsHorizontalUnitAdaptedFieldOn R (Real.sqrt a) (Real.sqrt b) (P i))
    (EP : ∀ i, M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) (P i))
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b)
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner (R.curve s) (P i s) (P j s) =
      if i = j then 1 else 0) :
    let q := spacetimeSlicePoint G.slices (R.curve s)
    let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
    (∑ i, pullbackIndexPairDensity R (horizontalAdaptedExtension (EP i))
      (horizontalAdaptedExtension (EP i)) s) =
      ((n : ℝ) - 4 * s * (s - Real.sqrt a) *
        horizontalScalarCurvature G.leafwise (R.curve s) +
        (s - Real.sqrt a) ^ 2 * (4 * s ^ 2 * D.ricciNormSq q +
          2 * s ^ 2 * D.laplacian D.scalarCurvature q -
            horizontalRicci G.leafwise (R.curve s) (R.horizontal_velocity s)
              (R.horizontal_velocity s))) / (Real.sqrt b - Real.sqrt a) ^ 2 := by
  obtain ⟨e, he⟩ := horizontalBasis_of_orthonormal (R.curve s) (fun i => P i s) horth
  let W : Fin n → G.Horizontal (R.curve s) := fun i =>
    M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval a b)
      (horizontalAdaptedField (Real.sqrt a) (Real.sqrt b) (P i))
      (horizontalAdaptedExtension (EP i)) s
  have hW (i : Fin n) (v : G.Horizontal (R.curve s)) :
      G.spacetime.horizontalMetric.inner (R.curve s) (W i) v =
        (1 / (Real.sqrt b - Real.sqrt a)) *
          G.spacetime.horizontalMetric.inner (R.curve s) (e i) v -
        2 * s * ((s - Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) *
          horizontalRicci G.leafwise (R.curve s) (e i) v := by
    rw [he]
    have h := horizontalAdaptedField_covariant_pair (hP i) (EP i) hs v
    exact h.trans (by ring)
  have h := horizontalIndexPairDensity_adapted_trace R hM04 s e
    (by simpa only [he] using horth) ((s - Real.sqrt a) / (Real.sqrt b - Real.sqrt a))
    (1 / (Real.sqrt b - Real.sqrt a)) W hW
  have hd : Real.sqrt b - Real.sqrt a ≠ 0 :=
    sub_ne_zero.mpr (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt).ne'
  calc
    _ = (n : ℝ) * (1 / (Real.sqrt b - Real.sqrt a)) ^ 2 -
        4 * s * ((s - Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) *
          (1 / (Real.sqrt b - Real.sqrt a)) *
            horizontalScalarCurvature G.leafwise (R.curve s) +
        ((s - Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) ^ 2 *
          (4 * s ^ 2 *
            (G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))).ricciNormSq
              (spacetimeSlicePoint G.slices (R.curve s)) +
            2 * s ^ 2 *
              (G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))).laplacian
              (G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))).scalarCurvature
              (spacetimeSlicePoint G.slices (R.curve s)) -
            horizontalRicci G.leafwise (R.curve s) (R.horizontal_velocity s)
              (R.horizontal_velocity s)) := by
      simpa only [he, pullbackIndexPairDensity, horizontalAdaptedField, W] using h
    _ = _ := by
      field_simp [hd]

end PoincareConjecture.M14
