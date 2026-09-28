import PoincareConjecture.Proofs.M14.Sec6_5_SharpIndexDefect
import PoincareConjecture.Proofs.M14.Sec6_5_IndexStationary
import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedScale

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 τ x y}
  (R : M14SquareRootPath G p)

theorem adaptedHessianPair_eq_of_index_equality
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : LinearMap.BilinForm ℝ (G.Horizontal (R.curve (Real.sqrt τ))))
    (hB : ∀ v w, B v w = B w v)
    (hbound : ∀ (W : ∀ s, G.Horizontal (R.curve s))
      (EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ) W),
      W (Real.sqrt 0) = 0 → (2 * Real.sqrt τ) * B (W (Real.sqrt τ)) (W (Real.sqrt τ)) ≤
        ∫ s in Real.sqrt 0..Real.sqrt τ, pullbackIndexPairDensity R EW EW s)
    {P Q : ∀ s, G.Horizontal (R.curve s)}
    (hP : IsHorizontalUnitAdaptedFieldOn R (Real.sqrt 0) (Real.sqrt τ) P)
    (EP : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ) P)
    (EQ : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ) Q)
    (heq : (∫ s in Real.sqrt 0..Real.sqrt τ,
      pullbackIndexPairDensity R (horizontalAdaptedExtension EP)
        (horizontalAdaptedExtension EP) s) =
      (2 * Real.sqrt τ) * B (P (Real.sqrt τ)) (P (Real.sqrt τ))) :
    horizontalRicci G.leafwise (R.curve (Real.sqrt τ)) (P (Real.sqrt τ)) (Q (Real.sqrt τ)) +
      B (P (Real.sqrt τ)) (Q (Real.sqrt τ)) =
        G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ))
          (P (Real.sqrt τ)) (Q (Real.sqrt τ)) / (2 * τ) := by
  let Y := horizontalAdaptedField (Real.sqrt 0) (Real.sqrt τ) P
  let Z := horizontalAdaptedField (Real.sqrt 0) (Real.sqrt τ) Q
  let EY := horizontalAdaptedExtension EP
  let EZ := horizontalAdaptedExtension EQ
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have ht : 0 < Real.sqrt τ := Real.sqrt_pos.mpr p.tau_lt
  obtain ⟨hY0, hYt⟩ := horizontalAdaptedField_endpoints (P := P) hab
  obtain ⟨hZ0, hZt⟩ := horizontalAdaptedField_endpoints (P := Q) hab
  have heq' : (∫ s in Real.sqrt 0..Real.sqrt τ, pullbackIndexPairDensity R EY EY s) =
      (2 * Real.sqrt τ) * B (Y (Real.sqrt τ)) (Y (Real.sqrt τ)) := by
    simpa only [Y, hYt] using heq
  have hpair (W : ∀ s, G.Horizontal (R.curve s))
      (EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ) W)
      (hW : W (Real.sqrt 0) = 0) :
      (∫ s in Real.sqrt 0..Real.sqrt τ, pullbackIndexPairDensity R EY EW s) =
        (2 * Real.sqrt τ) * B (P (Real.sqrt τ)) (W (Real.sqrt τ)) := by
    simpa only [Y, hYt] using pullbackIndexIntegral_eq_of_hessian_bound R hM04 hM12
      B hB (2 * Real.sqrt τ) hbound EY EW hY0 hW heq'
  have hstationary (W : ∀ s, G.Horizontal (R.curve s))
      (EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 τ) W)
      (hW0 : W (Real.sqrt 0) = 0) (hWt : W (Real.sqrt τ) = 0) :
      (∫ s in Real.sqrt 0..Real.sqrt τ, pullbackIndexPairDensity R EY EW s) = 0 := by
    rw [hpair W EW hW0, hWt, map_zero, mul_zero]
  let hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  let J := jacobiFieldDataOfExtension hCoordinates EY
  have hres {r : ℝ} (hr : r ∈ M14SqrtParameterInterval 0 τ)
      (V : G.Horizontal (R.curve r)) : M14JacobiResidual G R J r V = 0 :=
    jacobiResidual_eq_zero_of_index_stationary R hM04 hM12 EY hstationary hr V
  have hresint : (∫ r in Real.sqrt 0..Real.sqrt τ,
      M14JacobiResidual G R J r (Z r)) = 0 := by
    calc
      _ = ∫ r in Real.sqrt 0..Real.sqrt τ, (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le hab.le
          (fun r hr => hres (Ioo_subset_Icc_self hr) (Z r))
      _ = 0 := intervalIntegral.integral_zero
  have hg := integral_pullbackIndexPairDensity R J EZ hM04 hM12
  rw [hresint] at hg
  change (∫ r in Real.sqrt 0..Real.sqrt τ, pullbackIndexPairDensity R EY EZ r) =
    pullbackIndexBoundaryPair R EY Z (Real.sqrt τ) -
      pullbackIndexBoundaryPair R EY Z (Real.sqrt 0) - 0 at hg
  rw [hpair Z EZ hZ0] at hg
  simp only [pullbackIndexBoundaryPair, Z, hZ0, hZt, map_zero, sub_zero] at hg
  have hd := horizontalAdaptedField_covariant_pair hP EP
    (right_mem_Icc.mpr hab.le) (Q (Real.sqrt τ))
  simp only [Real.sqrt_zero, sub_zero, div_self ht.ne', mul_one] at hd
  have hvalue := hg.trans hd
  calc
    _ = G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ))
        (P (Real.sqrt τ)) (Q (Real.sqrt τ)) / (2 * (Real.sqrt τ) ^ 2) := by
      field_simp [ht.ne'] at hvalue ⊢
      nlinarith only [hvalue]
    _ = _ := by rw [Real.sq_sqrt p.tau_lt.le]

end PoincareConjecture.M14
