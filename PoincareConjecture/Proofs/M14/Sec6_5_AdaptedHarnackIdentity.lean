import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedScalarPrimitive










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem scalar_transport_smul {q r : G.Point} (h : q = r)
    (v : G.Horizontal r) (c : ℝ) :
    M14HorizontalScalarDifferential G q (h.symm ▸ (c • v)).val =
      c * M14HorizontalScalarDifferential G r v.val := by
  cases h
  change M14HorizontalScalarDifferential G q (c • v.val) = _
  rw [map_smul, smul_eq_mul]

private theorem ricci_transport_smul (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {q r : G.Point} (h : q = r) (v : G.Horizontal r) (c : ℝ) :
    horizontalRicci G.leafwise q (h.symm ▸ (c • v)) (h.symm ▸ (c • v)) =
      c ^ 2 * horizontalRicci G.leafwise r v v := by
  cases h
  rw [horizontalRicci_smul_left hM12, horizontalRicci_smul_right hM12]
  ring

variable {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}



theorem squareRoot_shiftedHarnackDensity_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
    2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * M14GeneralizedHarnackDensity G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) (s ^ 2) =
      -(2 * s ^ 2 * (s - Real.sqrt a) ^ 2) *
        M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) -
      2 * (s - Real.sqrt a) ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s) -
      2 * s * (s - Real.sqrt a) ^ 2 *
        M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val +
      (s - Real.sqrt a) ^ 2 * horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) := by
  have hsC : s ∈ M14SqrtParameterInterval a b := Ioo_subset_Icc_self hs
  have hbase := R.agrees s hsC
  have hscalar : M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val =
      (2 * s) * M14HorizontalScalarDifferential G (p.curve (s ^ 2))
        (p.horizontal_velocity (s ^ 2)).val := by
    rw [R.horizontal_agrees s hs]
    exact scalar_transport_smul hbase _ _
  have hricci : horizontalRicci G.leafwise (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s) =
        (2 * s) ^ 2 * horizontalRicci G.leafwise (p.curve (s ^ 2))
          (p.horizontal_velocity (s ^ 2)) (p.horizontal_velocity (s ^ 2)) := by
    rw [R.horizontal_agrees s hs]
    exact ricci_transport_smul hM12 hbase _ _
  rw [hscalar, hricci, hbase]
  unfold M14GeneralizedHarnackDensity M14HorizontalScalarDifferential
  have hs0 : s ≠ 0 := ((Real.sqrt_nonneg a).trans_lt hs.1).ne'
  field_simp [hs0]




theorem adaptedScalarPrimitive_add_shiftedHarnack
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
    derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) s +
      2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * M14GeneralizedHarnackDensity G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) (s ^ 2) =
      4 * s * (s - Real.sqrt a) * horizontalScalarCurvature G.leafwise (R.curve s) +
      2 * s ^ 2 * (s - Real.sqrt a) ^ 2 *
        M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) +
      (s - Real.sqrt a) ^ 2 * horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) := by
  rw [adaptedScalarPrimitive_derivWithin hM12 R (Ioo_subset_Icc_self hs),
    squareRoot_shiftedHarnackDensity_eq hM12 R hs]
  ring

end PoincareConjecture.M14
