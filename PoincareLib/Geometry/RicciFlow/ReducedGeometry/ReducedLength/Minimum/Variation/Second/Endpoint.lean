import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Minimality

/-!
# Natural endpoint conditions in second variation

An initial-fixed variation has zero initial endpoint acceleration. At a
free-endpoint minimum the terminal base velocity is also zero, so both second
variation boundary terms vanish. The scalar second-derivative test then gives
nonnegativity of the index form from the actual derivative formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareMT.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The acceleration of a curve constant on an open parameter set is zero,
independently of the chosen extension of its velocity. -/
theorem pullbackCovariantDerivative_velocity_eq_zero_of_constant
    {J I : Set ℝ} (F : RicciFlow n M J) (time : ℝ → ℝ)
    (hI : IsOpen I) (α : ℝ → M)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {s : ℝ} (hs : s ∈ I) (hconstant : EqOn α (fun _ ↦ α s) I) :
    pullbackCovariantDerivative F time α (curveVelocityWithin (n := n) α I) I E s = 0 := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hvelocity (r : ℝ) (hr : r ∈ I) : curveVelocityWithin (n := n) α I r = 0 := by
    have hnear : α =ᶠ[𝓝 r] fun _ ↦ α s := by
      filter_upwards [hI.mem_nhds hr] with u hu
      exact hconstant hu
    unfold curveVelocityWithin
    rw [mfderivWithin_of_mem_nhds (hI.mem_nhds hr), hnear.mfderiv_eq]
    simp only [mfderiv_const, zero_apply]
  have hext : (fun r ↦ E.extension r (α s)) =ᶠ[𝓝 s]
      (fun _ ↦ (0 : TangentSpace (𝓡 n) (α s))) := by
    filter_upwards [hI.mem_nhds hs] with r hr
    have hpoint : α r = α s := hconstant hr
    rw [← hpoint, E.agrees r hr, hvelocity r hr]
  unfold pullbackCovariantDerivative
  rw [hext.deriv_eq, deriv_const, hvelocity s hs]
  simp only [map_zero, add_zero]

/-- The initial square-time endpoint is fixed for every allowed parameter. -/
theorem initialFixed_squareFamily_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : InitialFixedLVariation F T a b p) {u : ℝ}
    (hu : u ∈ V.toLVariation.parameterDomain) :
    V.squareFamily (Real.sqrt a) u = p.curve a := by
  rw [V.square_agrees (Real.sqrt a) ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩ u hu,
    Real.sq_sqrt p.nonnegative]
  exact V.fixed_left u hu

/-- Fixing the initial endpoint forces its actual covariant acceleration to vanish. -/
theorem variationEndpointAcceleration_initial_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : InitialFixedLVariation F T a b p) (D : LVariationDerivativeData V.toLVariation)
    (ha : Real.sqrt a ∈ sqrtParameterInterval a b) :
    variationEndpointAcceleration V.toLVariation D (Real.sqrt a) ha = 0 := by
  have hzero : (0 : ℝ) ∈ V.toLVariation.parameterDomain :=
    ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  apply pullbackCovariantDerivative_velocity_eq_zero_of_constant F
    (fun _ ↦ T - (Real.sqrt a) ^ 2) isOpen_Ioo (V.squareFamily (Real.sqrt a))
    (D.endpoint_extension (Real.sqrt a) ha) hzero
  intro u hu
  exact (initialFixed_squareFamily_eq V hu).trans (initialFixed_squareFamily_eq V hzero).symm

/-- Both boundary contributions vanish under the natural free-endpoint conditions. -/
theorem secondVariationBoundaryTerm_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : InitialFixedLVariation F T a b p) (D : LVariationDerivativeData V.toLVariation)
    (hterminal : curveVelocityWithin (n := n) V.toLVariation.baseSquareCurve
      (sqrtParameterInterval a b) (Real.sqrt b) = 0) :
    secondVariationBoundaryTerm V.toLVariation D = 0 := by
  simp only [secondVariationBoundaryTerm, hterminal,
    variationEndpointAcceleration_initial_eq_zero V D, map_zero, zero_apply, sub_self]

end PoincareMT.ReducedLengthMinimum.Variation.Geometry

namespace PoincareMT.ReducedLengthMinimum.Variation

open Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The second derivative formula and actual path minimality imply a nonnegative index form. -/
theorem secondVariationIndexForm_nonneg_of_hasDerivAt {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (hmin : ∀ q : BackwardTimePath F T a b, q.curve a = p.curve a →
      backwardLLength F T a b p.curve ≤ backwardLLength F T a b q.curve)
    (V : InitialFixedLVariation F T a b p) (D : LVariationDerivativeData V.toLVariation)
    (hterminal : curveVelocityWithin (n := n) V.toLVariation.baseSquareCurve
      (sqrtParameterInterval a b) (Real.sqrt b) = 0)
    {d : ℝ} (hd : HasDerivAt (variationSquareAction V.toLVariation) d 0)
    (hdd : HasDerivAt (deriv (variationSquareAction V.toLVariation))
      (secondVariationBoundaryTerm V.toLVariation D + secondVariationIndexForm V.toLVariation D)
      0) :
    0 ≤ secondVariationIndexForm V.toLVariation D := by
  have h := secondVariation_nonneg hmin V hd hdd
  simpa only [secondVariationBoundaryTerm_eq_zero V D hterminal, zero_add] using h

end PoincareMT.ReducedLengthMinimum.Variation

namespace PoincareMT.AncientKappaSolution

open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Ancient action smoothness supplies the first derivative in the index-form test. -/
theorem secondVariationIndexForm_nonneg_of_hasDerivAt (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ}
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (V : InitialFixedLVariation K.flow 0 0 τ p) (D : LVariationDerivativeData V.toLVariation)
    (hterminal : curveVelocityWithin (n := 2) V.toLVariation.baseSquareCurve
      (sqrtParameterInterval 0 τ) (Real.sqrt τ) = 0)
    (hdd : HasDerivAt (deriv (variationSquareAction V.toLVariation))
      (secondVariationBoundaryTerm V.toLVariation D + secondVariationIndexForm V.toLVariation D)
      0) :
    0 ≤ secondVariationIndexForm V.toLVariation D := by
  have h := K.secondVariation_nonneg hmin V hdd
  simpa only [secondVariationBoundaryTerm_eq_zero V D hterminal, zero_add] using h

end PoincareMT.AncientKappaSolution
