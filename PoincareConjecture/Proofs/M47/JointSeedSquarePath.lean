import PoincareConjecture.Proofs.M08.ContinuationBackward
import PoincareConjecture.Proofs.M09.SquareComparisonDensity
import PoincareConjecture.Proofs.M47.JointSeedPath

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J}

private theorem square_density_eq_regularized (T : ℝ) (alpha : ℝ → M) :
    Proofs.M09.squareCurveActionDensity F T alpha = M08.regularizedLIntegrand F T alpha := rfl

theorem jointSeed_square_density_integrable
    (hM04 : RicciFlowCurvatureTheory.{u}) (T d : ℝ) (hd : 0 < d)
    (hwindow : Icc (T - d) T ⊆ J) (alpha : ℝ → M) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc 0 (Real.sqrt d) ⊆ U)
    (halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha U) :
    IntervalIntegrable (Proofs.M09.squareCurveActionDensity F T alpha) volume 0 (Real.sqrt d) := by
  apply M08.continuationAction_intervalIntegrable F hM04 T (Real.sqrt_nonneg d)
    hU hI alpha halpha
  intro s hs
  apply hwindow
  have hsquare : s ^ 2 ≤ d := by
    simpa only [Real.sq_sqrt hd.le] using
      (sq_le_sq₀ hs.1 (Real.sqrt_nonneg d)).2 hs.2
  constructor <;> nlinarith [sq_nonneg s]

theorem exists_jointSeed_closed_square_path
    (hM04 : RicciFlowCurvatureTheory.{u}) (T d : ℝ) (hd : 0 < d)
    (hwindow : Icc (T - d) T ⊆ J) (alpha : ℝ → M) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc 0 (Real.sqrt d) ⊆ U)
    (halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha U) :
    ∃ path : BackwardTimePath F T 0 d,
      path.curve = (fun tau => alpha (Real.sqrt tau)) ∧
      backwardLLength F T 0 d path.curve =
        ∫ s in 0..Real.sqrt d, Proofs.M09.squareCurveActionDensity F T alpha s := by
  have hT : T ∈ J := hwindow ⟨sub_le_self T hd.le, le_rfl⟩
  have htime : ∀ tau ∈ Icc 0 d, T - tau ∈ J := fun tau htau =>
    hwindow ⟨sub_le_sub_left htau.2 T, sub_le_self T htau.1⟩
  have hcont : ContinuousOn alpha (Icc (Real.sqrt 0) (Real.sqrt d)) := by
    simpa only [Real.sqrt_zero] using halpha.continuousOn.mono hI
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 alpha
      (Ioo (Real.sqrt 0) (Real.sqrt d)) := by
    simpa only [Real.sqrt_zero] using
      (halpha.of_le (by simp)).mono (Ioo_subset_Icc_self.trans hI)
  have hint : IntervalIntegrable (M08.regularizedLIntegrand F T alpha) volume
      (Real.sqrt 0) (Real.sqrt d) := by
    simpa only [Real.sqrt_zero, square_density_eq_regularized] using
      jointSeed_square_density_integrable (F := F) hM04 T d hd hwindow alpha hU hI halpha
  let path := M08.backwardPathOfSqrt F T 0 d le_rfl hd hT htime alpha hcont hreg hint
  refine ⟨path, rfl, ?_⟩
  simpa only [M08.regularizedLAction, Real.sqrt_zero, square_density_eq_regularized] using
    M08.backwardPathOfSqrt_action F T 0 d le_rfl hd hT htime alpha hcont hreg hint

def jointSeed_restrict_sqrt_path {T tau theta : ℝ}
    {path : BackwardTimePath F T 0 tau} (R : SqrtRegularPath path)
    (htheta : 0 < theta) (hle : theta ≤ tau) :
    SqrtRegularPath (jointSeed_restrict_path path htheta hle) where
  curve := R.curve
  domain := R.domain
  open_domain := R.open_domain
  interval_subset := (Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hle)).trans R.interval_subset
  smooth := R.smooth
  agrees := fun s hs => R.agrees s ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt hle)⟩

theorem jointSeed_restricted_square_action {T tau theta : ℝ}
    {path : BackwardTimePath F T 0 tau} (R : SqrtRegularPath path)
    (htheta : 0 < theta) (hle : theta ≤ tau) :
    (∫ s in 0..Real.sqrt theta, Proofs.M09.squareCurveActionDensity F T R.curve s) =
      backwardLLength F T 0 theta (jointSeed_restrict_path path htheta hle).curve := by
  simpa only [M08.regularizedLAction, Real.sqrt_zero, square_density_eq_regularized,
    jointSeed_restrict_sqrt_path] using
    M08.regularizedLAction_eq_backwardLLength (jointSeed_restrict_sqrt_path R htheta hle)

end PoincareConjecture.M47
