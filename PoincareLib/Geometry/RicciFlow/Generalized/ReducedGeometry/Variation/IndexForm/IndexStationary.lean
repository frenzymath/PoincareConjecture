import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexJacobi
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexAlgebra
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.PullbackScalar
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.IntervalTestFunctions
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Manifold.SectionThroughVector

/-!
# Index stationarity and the actual closed Jacobi equation

Green's identity tests the supplied first extension against smooth
fields vanishing at both endpoints. Scalar cutoffs detect the continuous
Jacobi residual on the entire closed square interval. Morgan-Tian
Proposition 6.13, Lemma 6.14 and Corollary 6.16, pp. 110-112, and the
sharp endpoint Hessian argument in Section 6.5, pp. 126-127.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

/-- Stationarity against every zero-endpoint actual test field forces
the supplied Jacobi data to solve the actual pair equation at every
closed point, Proposition 6.13 and Lemma 6.14, pp. 110-112. -/
theorem jacobiResidual_eq_zero_of_index_pair_stationary
    (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂))
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hstationary : ∀ W : ∀ r, G.Horizontal (R.curve r),
      ∀ EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) W,
        W (Real.sqrt τ₁) = 0 → W (Real.sqrt τ₂) = 0 →
          (∫ r in Real.sqrt τ₁..Real.sqrt τ₂,
            pullbackIndexPairDensity R Q.extension EW r) = 0)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (V : G.Horizontal (R.curve s)) : M14JacobiResidual G R Q s V = 0 := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨A, hA, hAs⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) V
  obtain ⟨EA⟩ := exists_pullbackExtension_Icc (G := G) (γ := R.curve)
    (Y := fun r => A (R.curve r)) hab
      (hA.comp_contMDiffOn (R.smooth.mono R.interval_subset))
  have hcont := (jacobiResidual_contDiffOn R Q EA hM04 hM12).continuousOn
  have hzero : EqOn (fun r => M14JacobiResidual G R Q r (A (R.curve r)))
      0 (M14SqrtParameterInterval τ₁ τ₂) := by
    apply hcont.eq_zero_of_intervalIntegral_contDiff_smul hab
    intro ψ hψ _ hsupp
    have hleft : ψ (Real.sqrt τ₁) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl _ (hsupp h).1))
    have hright : ψ (Real.sqrt τ₂) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl _ (hsupp h).2))
    let Eψ := smulPullbackExtension EA ψ hψ
    have hpair := hstationary _ Eψ
      (by simp only [hleft, zero_smul]) (by simp only [hright, zero_smul])
    have hgreen := integral_pullbackIndexPairDensity R Q Eψ hM04 hM12
    rw [hpair] at hgreen
    simp only [pullbackIndexBoundaryPair, hleft, hright, zero_smul, map_zero,
      sub_self, zero_sub] at hgreen
    have hres : (∫ r in Real.sqrt τ₁..Real.sqrt τ₂,
        M14JacobiResidual G R Q r (ψ r • A (R.curve r))) = 0 :=
      neg_eq_zero.mp hgreen.symm
    rw [← hres]
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro r hr
    exact (horizontalJacobiPairResidual_smul_right R hM04 hM12
      (Ioo_subset_Icc_self hr) (Q.field r) (M14JacobiFirstDerivative Q r)
      (M14JacobiSecondDerivative Q r) (A (R.curve r)) (ψ r)).symm
  simpa only [hAs, Pi.zero_apply] using hzero hs

/-- Index stationarity gives the actual Jacobi equation while retaining
the supplied first extension exactly, including both endpoints and
initial time zero, Proposition 6.13 and Lemma 6.14, pp. 110-112. -/
theorem jacobiResidual_eq_zero_of_index_stationary
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {Y : ∀ r, G.Horizontal (R.curve r)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (hstationary : ∀ W : ∀ r, G.Horizontal (R.curve r),
      ∀ EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) W,
        W (Real.sqrt τ₁) = 0 → W (Real.sqrt τ₂) = 0 →
          (∫ r in Real.sqrt τ₁..Real.sqrt τ₂,
            pullbackIndexPairDensity R EY EW r) = 0)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (V : G.Horizontal (R.curve s)) :
    let Q := jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) EY
    M14JacobiResidual G R Q s V = 0 :=
  jacobiResidual_eq_zero_of_index_pair_stationary R
    (jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) EY) hM04 hM12 hstationary hs V

end PoincareMT.M14
