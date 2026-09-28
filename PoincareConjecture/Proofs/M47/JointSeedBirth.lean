import PoincareConjecture.Proofs.M47.JointSeedJoin
import PoincareConjecture.Proofs.M47.JointSeedConstantAction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J}

theorem jointSeed_birth_reducedLength_of_worldline
    (hM04 : RicciFlowCurvatureTheory.{u}) {T d eta v K B : ℝ}
    (hd : 0 < d) (heta : 0 < eta) (hetaV : eta < v) (hvd : v < d)
    (hK : 0 ≤ K) (hwindow : Icc (T - d) T ⊆ J)
    (hL : LGeodesicTheory F T d) (x : M) (path : BackwardTimePath F T 0 (d - eta))
    (hstart : path.curve 0 = x) (hmin : IsMinimizingBackwardLPath F T 0 (d - eta) path)
    (haction : backwardLLength F T 0 (d - eta) path.curve ≤ B)
    (hscalar : ∀ t ∈ J, ∀ y : M, 0 ≤ (F.connection t).scalarCurvature y)
    (hworldline : ∀ t ∈ Icc (T - d) (T - d + v),
      (F.connection t).scalarCurvature (path.curve (d - v)) ≤ K) :
    reducedLength F T x (path.curve (d - v)) d ≤
      (B + K * v * Real.sqrt d) / (2 * Real.sqrt d) := by
  have hv : 0 < v := heta.trans hetaV
  have htheta : 0 < d - v := sub_pos.mpr hvd
  have hthetaPath : d - v ≤ d - eta := by linarith
  have hpathMax : d - eta ≤ d := sub_le_self _ heta.le
  obtain ⟨Rdata⟩ := hL.regularized_geodesic 0 (d - eta) le_rfl path.ordered hpathMax path
    (hL.euler_lagrange 0 (d - eta) le_rfl path.ordered hpathMax path hmin)
  let R := Rdata.path
  let q := path.curve (d - v)
  let c := Real.sqrt (d - v)
  let b0 := Real.sqrt (d - eta)
  have hc : 0 < c := Real.sqrt_pos.mpr htheta
  have hcb : c < b0 := Real.sqrt_lt_sqrt htheta.le (by linarith)
  have hb : b0 < Real.sqrt d := Real.sqrt_lt_sqrt path.ordered.le (sub_lt_self _ heta)
  have hIa : Icc 0 b0 ⊆ R.domain := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using R.interval_subset
  have hRzero : R.curve 0 = x := by
    have h := R.agrees 0 (show (0 : ℝ) ∈ sqrtParameterInterval 0 (d - eta) by
      exact ⟨by simp, Real.sqrt_nonneg _⟩)
    exact (h.trans (congrArg path.curve (zero_pow two_ne_zero))).trans hstart
  have hRc : R.curve c = q := by
    have h := R.agrees c (show c ∈ sqrtParameterInterval 0 (d - eta) by
      exact ⟨by simpa only [Real.sqrt_zero] using hc.le, hcb.le⟩)
    simpa only [c, Real.sq_sqrt htheta.le] using h
  have hleftAction : (∫ s in 0..c, Proofs.M09.squareCurveActionDensity F T R.curve s) ≤ B :=
    (jointSeed_restricted_square_action R htheta hthetaPath).trans_le
      ((jointSeed_restricted_action_le path htheta hthetaPath hscalar).trans haction)
  have hrightAction := jointSeed_constant_square_action_le
    (F := F) hM04 T d v K q hd hv hvd hK hwindow hworldline
  have hden : 0 < 2 * Real.sqrt d := by positivity
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨competitor, hzero, hend, hcost⟩ := exists_jointSeed_smooth_join
    (F := F) hM04 T d b0 c hd hwindow hc hcb hb R.curve (fun _ => q)
    R.open_domain isOpen_univ hIa (subset_univ _) R.smooth contMDiffOn_const hRc
    (eps * (2 * Real.sqrt d)) (mul_pos heps hden)
  have hcost' : backwardLLength F T 0 d competitor.curve ≤
      B + K * v * Real.sqrt d + eps * (2 * Real.sqrt d) := by
    linarith
  have hred := Proofs.M09.reducedLength_le_path hL hd le_rfl competitor
    (hzero.trans hRzero) hend
  have hquot : (B + K * v * Real.sqrt d + eps * (2 * Real.sqrt d)) /
      (2 * Real.sqrt d) = (B + K * v * Real.sqrt d) / (2 * Real.sqrt d) + eps := by
    rw [add_div, mul_div_cancel_right₀ _ hden.ne']
  exact hred.trans ((div_le_div_of_nonneg_right hcost' hden.le).trans_eq hquot)

end PoincareConjecture.M47
