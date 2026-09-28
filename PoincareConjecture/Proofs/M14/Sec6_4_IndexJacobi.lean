import PoincareConjecture.Proofs.M14.Sec6_4_IndexGreen










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}




noncomputable def jacobiFieldDataOfExtension
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y) :
    M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂) where
  field := Y
  extension := E
  derivative_extension :=
    Classical.choice (exists_horizontalCovariantDerivative_extension R hCoordinates E)



theorem index_zero_of_variationJacobiCondition
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hJacobi : M14VariationJacobiCondition V D) : M14SecondVariationIndexForm V D = 0 := by
  obtain ⟨Q, hfield, hE, hleft, hright, hres⟩ := hJacobi
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hpair : M14SecondVariationIndexForm V D =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        pullbackIndexPairDensity R Q.extension Q.extension s := by
    rcases Q with ⟨Y, E, ED⟩
    dsimp only at hfield hE ⊢
    cases hfield
    cases hE
    exact intervalIntegral.integral_congr_Ioo_of_le hab.le
      (fun s _ => secondVariationIndexDensity_eq_pair R V D s)
  have hG := integral_pullbackIndexPairDensity R Q Q.extension hM04 hM12
  have hresint : (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      M14JacobiResidual G R Q s (Q.field s)) = 0 := by
    rw [← intervalIntegral.integral_zero (μ := volume) (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)]
    exact intervalIntegral.integral_congr_Ioo_of_le hab.le
      (fun s hs => hres s (Ioo_subset_Icc_self hs) _)
  rw [hpair, hG, hresint]
  simp only [pullbackIndexBoundaryPair, hleft, hright, map_zero, sub_self]

end PoincareConjecture.M14
