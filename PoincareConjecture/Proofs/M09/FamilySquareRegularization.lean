import PoincareConjecture.Proofs.M09.FamilyEndpointEquation
import PoincareConjecture.Proofs.M09.CompactVelocityExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def lExponentialFamily_squarePath (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    SqrtRegularPath (A.path Z b hb hmax) where
  curve := A.squareFamily Z
  domain := (fun r : ℝ ↦ (Z, r)) ⁻¹' A.squareDomain
  open_domain := A.square_open.preimage (continuous_const.prodMk continuous_id)
  interval_subset := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact A.square_contains ⟨Set.mem_univ _, hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  smooth := lExponentialFamily_squareSlice_contMDiffOn A Z
  agrees := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact (A.square_agrees Z s ⟨hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩).trans
        (congrFun (A.path_eq Z b hb hmax) (s ^ 2)).symm

noncomputable def lExponentialFamily_squareRegularization
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    RegularizedLGeodesicData (A.path Z b hb hmax) := by
  let R := lExponentialFamily_squarePath A Z b hb hmax
  let K := sqrtParameterInterval 0 b
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (by norm_num) hb)
  let E := Classical.choice (nonempty_velocityExtensionOn_compact R.curve R.domain K
    R.open_domain R.interval_subset isCompact_Icc hKd R.smooth)
  refine { path := R, velocity_extension := E, equation := ?_ }
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  exact (regularizedEquation_iff_local F hM04 T τmax hτmax hwindow
    R.curve R.domain K R.open_domain R.interval_subset hKd R.smooth E s hs htime).mpr
      (lExponentialFamily_localRegularizedEquation_closed hM04 hτmax hwindow A Z b hb hmax s hs)

theorem lExponentialFamily_chartPhase_hasDerivAt
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (x0 : M) (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b)
    (hx : A.squareFamily Z s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x0).source) :
    let a : ℝ → EuclideanSpace ℝ (Fin n) :=
      fun r ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x0) (A.squareFamily Z r)
    HasDerivAt (fun r ↦ (a r, deriv a r))
      (regularizedCoordinatePhase (squareChartMetric F T x0) (squareChartScalar F T x0)
        (s, (a s, deriv a s))) s := by
  let R := lExponentialFamily_squareRegularization hM04 hτmax hwindow A Z b hb hmax
  let K := sqrtParameterInterval 0 b
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (by norm_num) hb)
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  exact (regularizedEquation_iff_chart_hasDerivAt F hM04 T τmax hτmax hwindow x0
    R.path.curve R.path.domain K R.path.open_domain R.path.interval_subset hKd
    R.path.smooth R.velocity_extension s hs htime hx).mp (R.equation s hs)

end PoincareConjecture.Proofs.M09
