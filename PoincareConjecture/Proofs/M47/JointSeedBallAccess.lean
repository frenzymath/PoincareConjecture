import PoincareConjecture.Proofs.M47.JointSeedRadialAction
import PoincareConjecture.Proofs.M47.JointSeedAccessScales
import PoincareConjecture.Proofs.M47.JointSeedBallContainment
import PoincareConjecture.Proofs.M47.JointSeedRadialPath
import PoincareConjecture.Proofs.M47.JointSeedJoin

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J}

theorem jointSeed_mid_age_reducedLength_on_birth_ball
    (hM04 : RicciFlowCurvatureTheory.{u}) {T d eta v K B r : ℝ}
    (hd : 0 < d) (heta : 0 < eta) (hetaV : eta < v) (hvd : v < d)
    (hK : 0 ≤ K) (hr : 0 < r) (hwindow : Icc (T - d) T ⊆ J)
    (hL : LGeodesicTheory F T d) (x : M) (path : BackwardTimePath F T 0 (d - eta))
    (hstart : path.curve 0 = x) (hmin : IsMinimizingBackwardLPath F T 0 (d - eta) path)
    (haction : backwardLLength F T 0 (d - eta) path.curve ≤ B)
    (hscalar : ∀ t ∈ J, ∀ z : M, 0 ≤ (F.connection t).scalarCurvature z)
    (hcompact : IsCompact (closure ((F.metric (T - d)).ball (path.curve (d - v)) r)))
    (hupper : ∀ t ∈ Icc (T - d) (T - d + v), ∀ z : M, ∀ w : TangentSpace (𝓡 n) z,
      (F.metric t).inner z w w ≤ (F.metric (T - d)).inner z w w)
    (hballscalar : ∀ t ∈ Icc (T - d) (T - d + v),
      ∀ z ∈ (F.metric (T - d)).ball (path.curve (d - v)) r,
        (F.connection t).scalarCurvature z ≤ K)
    (y : M) (hy : y ∈ (F.metric (T - d)).ball (path.curve (d - v)) r) :
    reducedLength F T x y (d - v / 2) ≤
      (B + (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d) /
        (2 * Real.sqrt (d - v / 2)) := by
  have hv : 0 < v := heta.trans hetaV
  have htheta : 0 < d - v / 2 := by linarith
  have hthetaMax : d - v / 2 ≤ d := by linarith
  have hpoint : 0 < d - v := sub_pos.mpr hvd
  have hpointPath : d - v ≤ d - eta := by linarith
  have hpathMax : d - eta ≤ d := sub_le_self _ heta.le
  obtain ⟨Rdata⟩ := hL.regularized_geodesic 0 (d - eta) le_rfl path.ordered hpathMax path
    (hL.euler_lagrange 0 (d - eta) le_rfl path.ordered hpathMax path hmin)
  let R := Rdata.path
  let q := path.curve (d - v)
  let c := Real.sqrt (d - v)
  have hc : 0 < c := Real.sqrt_pos.mpr hpoint
  have hcleft : c < Real.sqrt (d - eta) := Real.sqrt_lt_sqrt hpoint.le (by linarith)
  have hcright : c < Real.sqrt (d - v / 2) := Real.sqrt_lt_sqrt hpoint.le (by linarith)
  obtain ⟨b0, hcb, hb⟩ := exists_between (lt_min hcleft hcright)
  have hbLeft : b0 < Real.sqrt (d - eta) := hb.trans_le (min_le_left _ _)
  have hbRight : b0 < Real.sqrt (d - v / 2) := hb.trans_le (min_le_right _ _)
  have hIa : Icc 0 b0 ⊆ R.domain := by
    intro s hs
    apply R.interval_subset
    exact ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans hbLeft.le⟩
  have hRzero : R.curve 0 = x := by
    have h := R.agrees 0 (show (0 : ℝ) ∈ sqrtParameterInterval 0 (d - eta) by
      exact ⟨by simp, Real.sqrt_nonneg _⟩)
    exact (h.trans (congrArg path.curve (zero_pow two_ne_zero))).trans hstart
  have hRc : R.curve c = q := by
    have h := R.agrees c (show c ∈ sqrtParameterInterval 0 (d - eta) by
      exact ⟨by simpa only [Real.sqrt_zero] using hc.le, hcleft.le⟩)
    simpa only [c, Real.sq_sqrt hpoint.le] using h
  obtain ⟨gamma, hgamma, hgamma0, hgamma1, hmap, hspeed⟩ :=
    exists_jointSeed_radial_path (F.metric (T - d)) q y hr hcompact hy
  let beta (s : ℝ) := gamma (2 * (s ^ 2 - (d - v)) / v)
  have hbeta := jointSeed_radial_square_curve_smooth gamma hgamma d v
  have hbetac : beta c = q := by
    simp only [beta, c, Real.sq_sqrt hpoint.le, sub_self, mul_zero, zero_div, hgamma0]
  have hbetaEnd : beta (Real.sqrt (d - v / 2)) = y := by
    dsimp only [beta]
    rw [Real.sq_sqrt htheta.le]
    have hparameter : 2 * (d - v / 2 - (d - v)) / v = 1 := by field_simp; ring
    rw [hparameter, hgamma1]
  have hleftAction : (∫ s in 0..c, Proofs.M09.squareCurveActionDensity F T R.curve s) ≤ B :=
    (jointSeed_restricted_square_action R hpoint hpointPath).trans_le
      ((jointSeed_restricted_action_le path hpoint hpointPath hscalar).trans haction)
  have hrightAction := jointSeed_radial_square_action_le hM04 F (F.metric (T - d))
    T d v K r hd hv hvd hK hr.le hwindow gamma hgamma hmap
    (fun s hs => (hspeed s hs).le) (fun t ht z _hz w => hupper t ht z w) hballscalar
  have hsmallWindow : Icc (T - (d - v / 2)) T ⊆ J :=
    (Icc_subset_Icc (by linarith) le_rfl).trans hwindow
  have hden : 0 < 2 * Real.sqrt (d - v / 2) := by positivity
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨competitor, hzero, hend, hcost⟩ := exists_jointSeed_smooth_join
    (F := F) hM04 T (d - v / 2) b0 c htheta hsmallWindow hc hcb hbRight R.curve beta
    R.open_domain isOpen_univ hIa (subset_univ _) R.smooth hbeta.contMDiffOn
    (hRc.trans hbetac.symm) (eps * (2 * Real.sqrt (d - v / 2))) (mul_pos heps hden)
  have hcost' : backwardLLength F T 0 (d - v / 2) competitor.curve ≤
      B + (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d +
        eps * (2 * Real.sqrt (d - v / 2)) := by
    linarith
  have hred := Proofs.M09.reducedLength_le_path hL htheta hthetaMax competitor
    (hzero.trans hRzero) (hend.trans hbetaEnd)
  have hquot : (B + (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d +
      eps * (2 * Real.sqrt (d - v / 2))) / (2 * Real.sqrt (d - v / 2)) =
      (B + (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d) /
        (2 * Real.sqrt (d - v / 2)) + eps := by
    rw [add_div, mul_div_cancel_right₀ _ hden.ne']
  exact hred.trans ((div_le_div_of_nonneg_right hcost' hden.le).trans_eq hquot)

theorem jointSeed_mid_age_ball_access [CompactSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) {T d eta v A B L a : ℝ}
    (hd : 0 < d) (heta : 0 < eta) (hetaV : eta < v) (hvd : v ≤ d / 2)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hLpos : 0 < L) (ha : 0 < a) (hav : a ≤ v)
    (hwindow : Icc (T - d) T ⊆ J) (hL : LGeodesicTheory F T d)
    (x : M) (path : BackwardTimePath F T 0 (d - eta))
    (hstart : path.curve 0 = x) (hmin : IsMinimizingBackwardLPath F T 0 (d - eta) path)
    (haction : backwardLLength F T 0 (d - eta) path.curve ≤ 3 * Real.sqrt d)
    (hscalar : ∀ t ∈ J, ∀ z : M, 0 ≤ (F.connection t).scalarCurvature z)
    (hsec : ∀ t ∈ Icc (T - d) (T - d + v), ∀ z : M, ∀ w w' : TangentSpace (𝓡 n) z,
      0 ≤ (F.connection t).curvatureTensor z w w' w w')
    (hballscalar : ∀ z ∈ closure ((F.metric (T - d)).ball (path.curve (d - v))
        (Real.sqrt a / (4 * A * B))),
      ∀ t ∈ Icc (T - d) (T - d + v), (F.connection t).scalarCurvature z ≤ 8 * L)
    (hbudget : A * L * v ≤ 1 / 64) :
    ∀ y ∈ (F.metric (T - d + v / 2)).ball (path.curve (d - v))
        ((Real.sqrt a / (4 * A * B)) / 2),
      reducedLength F T x y (d - v / 2) ≤ 2 := by
  let r := Real.sqrt a / (4 * A * B)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hv : 0 < v := heta.trans hetaV
  have hvd' : v < d := by linarith
  have htime : Icc (T - d) (T - d + v) ⊆ J :=
    (Icc_subset_Icc le_rfl (by linarith)).trans hwindow
  have hupper (t : ℝ) (ht : t ∈ Icc (T - d) (T - d + v)) (z : M)
      (w : TangentSpace (𝓡 n) z) :
      (F.metric t).inner z w w ≤ (F.metric (T - d)).inner z w w :=
    jointSeed_metric_upper_of_nonnegative_sectional F ht.1
      ((Icc_subset_Icc le_rfl ht.2).trans htime)
      (fun s hs => hsec s ((Icc_subset_Icc le_rfl ht.2) hs)) z w
  have hmid : T - d + v / 2 ∈ Icc (T - d) (T - d + v) := ⟨by linarith, by linarith⟩
  have hmetric := jointSeed_early_metric_bounds F hA hLpos hv.le htime hsec hballscalar hbudget
  have hinclusions := jointSeed_seed_ball_inclusions (F.metric (T - d))
    (F.metric (T - d + v / 2)) (path.curve (d - v)) hr (hupper _ hmid)
    (fun z hz w => (hmetric _ hmid z hz w).1)
  intro y hy
  have hbirth := hinclusions.2 hy
  have hred := jointSeed_mid_age_reducedLength_on_birth_ball hM04 hd heta hetaV hvd'
    (by positivity : 0 ≤ 8 * L) hr hwindow hL x path hstart hmin haction hscalar
    (isClosed_closure.isCompact) hupper
    (fun t ht z hz => hballscalar z (subset_closure hz) t ht) y hbirth
  have hkinetic := jointSeed_radial_radius_action_budget hA hB ha hav
  have hscalarBudget := jointSeed_radial_scalar_action_budget hA hLpos.le hv.le hbudget
  have hnorm := jointSeed_mid_age_action_normalization hd hv hvd hscalarBudget hkinetic
  have hweaken : (3 * Real.sqrt d + ((8 * L) * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d) /
        (2 * Real.sqrt (d - v / 2)) ≤
      (3 * Real.sqrt d + (8 * L * v + 2 * r ^ 2 / v) * Real.sqrt d) /
        (2 * Real.sqrt (d - v / 2)) := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have h := mul_nonneg hLpos.le hv.le
    have hmul := mul_le_mul_of_nonneg_right
      (show (8 * L) * v / 2 + 2 * r ^ 2 / v ≤ 8 * L * v + 2 * r ^ 2 / v by nlinarith)
      (Real.sqrt_nonneg d)
    linarith
  exact (hred.trans hweaken).trans hnorm.le

end PoincareConjecture.M47
