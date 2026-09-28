import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Endpoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Integral
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Congruence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.DerivativeData










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem baseSquareCurve_eqOn_sqrtRegularPath {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : LVariation F T a b p) (S : SqrtRegularPath p) :
    EqOn V.baseSquareCurve S.curve (sqrtParameterInterval a b) := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain :=
    ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  intro s hs
  exact (V.square_agrees s hs 0 hzero).trans ((V.at_zero (s ^ 2)).trans (S.agrees s hs).symm)

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem secondVariationIndexForm_nonneg_and_integrable (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ} (S : SqrtRegularPath p)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (V : InitialFixedLVariation K.flow 0 0 τ p) (D : LVariationDerivativeData V.toLVariation) :
    0 ≤ secondVariationIndexForm V.toLVariation D ∧
      IntervalIntegrable (secondVariationIndexDensity V.toLVariation D) volume 0 (Real.sqrt τ) := by
  let C := sqrtParameterInterval 0 τ
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  let EC : ParametricAlongCurveExtensionOn C S.curve
      (curveVelocityWithin (n := 2) S.curve C) := {
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := fun s hs ↦ E.graph_mem s (by
      simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs)
    smooth := E.smooth
    agrees := fun s hs ↦ by
      have h := E.agrees s (by simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs)
      simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using h }
  have hbase := baseSquareCurve_eqOn_sqrtRegularPath V.toLVariation S
  have hEulerV (s : ℝ) (hs : s ∈ Ioo (Real.sqrt 0) (Real.sqrt τ))
      (W : TangentSpace (𝓡 2) (V.toLVariation.baseSquareCurve s)) :
      regularizedEulerResidual K.flow 0 V.toLVariation.baseSquareCurve C
        D.velocity_extension s W = 0 := by
    have hsC : s ∈ C := Ioo_subset_Icc_self hs
    have hSs := ((S.smooth s (S.interval_subset hsC)).contMDiffAt
      (S.open_domain.mem_nhds (S.interval_subset hsC))).mdifferentiableAt (by simp)
    have hcongr := regularizedEulerResidual_congr K.flow 0 hbase D.velocity_extension EC hsC
      (hC s hsC) hSs W
    rw [hcongr]
    have h := heuler s (by simpa only [Real.sqrt_zero] using hs) W
    simpa only [regularizedEulerResidual, pullbackCovariantDerivative, EC, C,
      sqrtParameterInterval, Real.sqrt_zero] using h
  have hterminalV : curveVelocityWithin (n := 2) V.toLVariation.baseSquareCurve C
      (Real.sqrt τ) = 0 := by
    rw [curveVelocityWithin_congr hbase
      (show Real.sqrt τ ∈ C from ⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩)]
    simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hterminal
  have hclock (s : ℝ) (_hs : s ∈ C) :
      s ∈ interior ((fun r : ℝ => 0 - r ^ 2) ⁻¹' Iic (0 : ℝ)) := by
    have hpre : ((fun r : ℝ => 0 - r ^ 2) ⁻¹' Iic (0 : ℝ)) = univ := by
      ext r
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      nlinarith [sq_nonneg r]
    rw [hpre, interior_univ]
    exact mem_univ s
  have htime (s : ℝ) (hs : s ∈ Ioo (Real.sqrt 0) (Real.sqrt τ)) :
      0 - s ^ 2 ∈ interior (Iic (0 : ℝ)) := by
    rw [Real.sqrt_zero] at hs
    rw [interior_Iic]
    exact sub_neg.mpr (sq_pos_of_pos hs.1)
  have hdd := hasDerivAt_secondVariation K.regularizedPotential_contMDiff
    hclock htime V.toLVariation D hEulerV
  refine ⟨K.secondVariationIndexForm_nonneg_of_hasDerivAt hmin V D hterminalV hdd, ?_⟩
  simpa only [Real.sqrt_zero] using
    secondVariationIndexDensity_intervalIntegrable K.regularizedPotential_contMDiff
      hclock htime V.toLVariation D hEulerV


theorem secondVariationIndexForm_nonneg (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ} (S : SqrtRegularPath p)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (V : InitialFixedLVariation K.flow 0 0 τ p) (D : LVariationDerivativeData V.toLVariation) :
    0 ≤ secondVariationIndexForm V.toLVariation D :=
  (K.secondVariationIndexForm_nonneg_and_integrable S E hmin heuler hterminal V D).1


theorem exists_nonneg_secondVariationIndexForm (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ} (S : SqrtRegularPath p)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (V : InitialFixedLVariation K.flow 0 0 τ p) :
    ∃ D : LVariationDerivativeData V.toLVariation,
      0 ≤ secondVariationIndexForm V.toLVariation D ∧
      IntervalIntegrable (secondVariationIndexDensity V.toLVariation D) volume 0 (Real.sqrt τ) := by
  obtain ⟨D⟩ := exists_variationDerivativeData V.toLVariation
  exact ⟨D, K.secondVariationIndexForm_nonneg_and_integrable S E hmin heuler hterminal V D⟩

end PoincareConjecture.AncientKappaSolution
