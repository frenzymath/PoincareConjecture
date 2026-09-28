import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Minimizer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Construction.CompactField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def fieldIndexDensity {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (α : ℝ → M)
    (C : Set ℝ) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (H : ParametricAlongCurveExtensionOn C α Y) (s : ℝ) : ℝ :=
  let A := curveVelocityWithin (n := n) α C s
  let DY := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C H s
  let connection := F.connection (T - s ^ 2)
  (F.metric (T - s ^ 2)).inner (α s) DY DY +
    connection.curvatureTensor (α s) (Y s) A A (Y s) +
    2 * s ^ 2 * connection.hessian connection.scalarCurvature (α s) (Y s) (Y s) -
    4 * s * ricciDerivativePairing connection (α s) (Y s) A (Y s) +
    2 * s * ricciDerivativePairing connection (α s) A (Y s) (Y s)

theorem secondVariationIndexDensity_eq_fieldIndexDensity
    {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : LVariation F T a b p) (D : LVariationDerivativeData V)
    (α : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (H : ParametricAlongCurveExtensionOn (sqrtParameterInterval a b) α Y)
    (hcurve : EqOn V.baseSquareCurve α (sqrtParameterInterval a b))
    (hfield : ∀ s ∈ sqrtParameterInterval a b, squareVariationField V s = Y s)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    secondVariationIndexDensity V D s = fieldIndexDensity F T α (sqrtParameterInterval a b) Y H s := by
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hs
  have hderivative := pullbackCovariantDerivative_congr F (fun r ↦ T - r ^ 2)
    hcurve hfield D.variation_extension H hs hC hα
  unfold secondVariationIndexDensity fieldIndexDensity
  dsimp only
  rw [hderivative, curveVelocityWithin_congr hcurve hs, hfield s hs, hcurve hs]

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem fieldIndexDensity_integrable_and_integral_nonneg (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ} (S : SqrtRegularPath p)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (Y : ∀ s, TangentSpace (𝓡 2) (S.curve s)) (U : Set ℝ)
    (hU : IsOpen U) (hCU : Icc 0 (Real.sqrt τ) ⊆ U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s ↦ (⟨S.curve s, Y s⟩ : TangentBundle (𝓡 2) M)) U)
    (hY0 : Y 0 = 0)
    (H : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve Y) :
    IntervalIntegrable (fieldIndexDensity K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) Y H)
      volume 0 (Real.sqrt τ) ∧
    0 ≤ ∫ s in (0 : ℝ)..Real.sqrt τ,
      fieldIndexDensity K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) Y H s := by
  let C := sqrtParameterInterval 0 τ
  let O := U ∩ S.domain
  have hO : IsOpen O := hU.inter S.open_domain
  have hCO : Icc 0 (Real.sqrt τ) ⊆ O := by
    intro s hs
    exact ⟨hCU hs, S.interval_subset (by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs)⟩
  have hagrees (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt τ)) : S.curve s = p.curve (s ^ 2) :=
    S.agrees s (by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs)
  obtain ⟨V, hbase, hfield⟩ := K.exists_initialFixedLVariation_of_smooth_field
    p S.curve Y O hO hCO (S.smooth.mono inter_subset_right)
    (hY.mono inter_subset_left) hagrees hY0
  obtain ⟨D, hindex, hint⟩ := K.exists_nonneg_secondVariationIndexForm
    S E hmin heuler hterminal V
  let HC : ParametricAlongCurveExtensionOn C S.curve Y := {
    extension := H.extension
    domain := H.domain
    open_domain := H.open_domain
    graph_mem := fun s hs ↦ H.graph_mem s (by
      simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs)
    smooth := H.smooth
    agrees := fun s hs ↦ H.agrees s (by
      simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs) }
  have hcurve : EqOn V.toLVariation.baseSquareCurve S.curve C :=
    fun s _ ↦ congrFun hbase s
  have hfieldC (s : ℝ) (hs : s ∈ C) : squareVariationField V.toLVariation s = Y s :=
    hfield s (by simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs)
  have hdensity (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt τ)) :
      secondVariationIndexDensity V.toLVariation D s =
        fieldIndexDensity K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) Y H s := by
    have hsC : s ∈ C := by simpa only [C, sqrtParameterInterval, Real.sqrt_zero] using hs
    have hSs := ((S.smooth s (S.interval_subset hsC)).contMDiffAt
      (S.open_domain.mem_nhds (S.interval_subset hsC))).mdifferentiableAt (by simp)
    have h := secondVariationIndexDensity_eq_fieldIndexDensity V.toLVariation D
      S.curve Y HC hcurve hfieldC hsC hSs
    simpa only [fieldIndexDensity, pullbackCovariantDerivative, HC, C,
      sqrtParameterInterval, Real.sqrt_zero] using h
  have hcongr : EqOn (secondVariationIndexDensity V.toLVariation D)
      (fieldIndexDensity K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) Y H)
      (uIoo 0 (Real.sqrt τ)) := by
    rw [uIoo_of_le (Real.sqrt_nonneg τ)]
    exact fun s hs ↦ hdensity s (Ioo_subset_Icc_self hs)
  refine ⟨hint.congr_uIoo hcongr, ?_⟩
  have hindex' : 0 ≤ ∫ s in (0 : ℝ)..Real.sqrt τ, secondVariationIndexDensity V.toLVariation D s := by
    simpa only [secondVariationIndexForm, Real.sqrt_zero] using hindex
  rwa [intervalIntegral.integral_congr_uIoo hcongr] at hindex'

end PoincareConjecture.AncientKappaSolution
