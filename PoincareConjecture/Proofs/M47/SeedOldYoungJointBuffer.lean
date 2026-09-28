import PoincareConjecture.Proofs.M47.SeedOldHistoryAnalytics
import PoincareConjecture.Proofs.M47.JointSeedPoint
import PoincareConjecture.Proofs.M47.JointSeedBallScales
import PoincareConjecture.Proofs.M47.JointSeedBallAccess










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_old_young_joint_buffer
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p) :
    ∃ A alpha B : ℝ, 1 ≤ A ∧ 0 < alpha ∧ alpha < 1 / 2 ∧ 1 ≤ B ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ (b T : ℝ), b < T → T - b ≤ (p.r (Fin.last p.i)) ^ 2 / (32 * A) →
          T ≤ surgeryEpochStart p.i → Icc b T ⊆ surgeryObservationInterval O →
          ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
            IsCompact (U : Set (F.slice T).carrier) →
            IsConnected (U : Set (F.slice T).carrier) →
            ∀ (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (b - T) 0) U)
              (G : RicciFlow 3 U (Icc b T)),
              (∀ s (hs : s ∈ Icc (b - T) 0) (y : U) (v w : TangentSpace (𝓡 3) y),
                (F.metric (T + s / 1)).inner (e.forward s hs y.val)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                    (G.metric (T + s / 1)).inner y v w) →
              (∀ s (hs : s ∈ Icc (b - T) 0) (y : U),
                (G.connection (T + s / 1)).scalarCurvature y =
                  (F.connection (T + s / 1)).scalarCurvature (e.forward s hs y.val)) →
              (∀ t ∈ Icc b T, ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
                0 ≤ (G.connection t).curvatureTensor y v w v w) →
              ∀ x : U, ∃ (v : ℝ) (q : U),
                v ∈ Icc (alpha * (T - b)) ((T - b) / 2) ∧
                (∀ z ∈ closure ((G.metric b).ball q (Real.sqrt (alpha * (T - b)) / (4 * A))),
                  (G.connection b).scalarCurvature z ≤ 4 * B / (T - b)) ∧
                (∀ z ∈ closure ((G.metric b).ball q (Real.sqrt (alpha * (T - b)) / (4 * A))),
                  ∀ s ∈ Icc b (b + v), (G.connection s).scalarCurvature z ≤ 8 * B / (T - b)) ∧
                (∀ y ∈ (G.metric (b + v / 2)).ball q
                    ((Real.sqrt (alpha * (T - b)) / (4 * A)) / 2),
                  reducedLength G T x y (T - b - v / 2) ≤ 2) ∧
                3 * (T - b) / 4 ≤ T - b - v / 2 ∧ T - b - v / 2 < T - b := by
  obtain ⟨A, hA, _hCA, hanalytic⟩ := exists_seed_old_history_analytic_bound P S p compatible
  let rho := p.r (Fin.last p.i)
  have hrho : 0 < rho := p.r_pos _
  let C := S.setup.C
  have hC : 1 ≤ C := S.setup.C_large
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hApos : 0 < A := zero_lt_one.trans_le hA
  let c := 1 / (64 * A * C)
  let alpha := Real.exp (-5 / c) / 2
  let B := max 1 (C * c / alpha)
  have hc : 0 < c := by dsimp only [c]; positivity
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have halphaHalf : alpha < 1 / 2 := by
    have hexp : Real.exp (-5 / c) < 1 :=
      Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hc)
    dsimp only [alpha]
    linarith only [hexp]
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨A, alpha, B, hA, halpha, halphaHalf, hB, ?_⟩
  intro F O old b T hbT hyoung hTold hobs U hcompact hconnected e G metric scalar hsec x
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  let d := T - b
  let sigma := d / 2
  let a := alpha * d
  let eta := a / 2
  have hd : 0 < d := sub_pos.mpr hbT
  have hsigma : 0 < sigma := half_pos hd
  have ha : 0 < a := mul_pos halpha hd
  have heta : 0 < eta := half_pos ha
  have hetaA : eta < a := half_lt_self ha
  have hae : a = sigma * Real.exp (-5 / c) := by dsimp only [a, alpha, sigma]; ring
  have hnonnegative : ∀ s ∈ Icc b T, ∀ y : U, 0 ≤ (G.connection s).scalarCurvature y :=
    fun s hs y => M04.nonneg_scalar_of_nonnegativeSectionalAt (G.connection s) y (hsec s hs y)
  obtain ⟨hL, path, hstart, hmin, haction, v, hv, hvScalar, _hvBound, _hred⟩ :=
    M47.exists_jointSeed_point P.ordinary hbT hc hsigma le_rfl hae heta hetaA G hnonnegative x
  let q := path.curve (d - v)
  have hvpos : 0 < v := ha.trans_le hv.1
  have hvd : v ≤ d / 2 := hv.2
  have hvsmall : v ≤ rho ^ 2 / (64 * A) := by
    have hhalf := div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
    have hid : rho ^ 2 / (32 * A) / 2 = rho ^ 2 / (64 * A) := by ring
    rw [hid] at hhalf
    exact hvd.trans hhalf
  let L := max (rho⁻¹ ^ 2) (C * c / v)
  obtain ⟨hLpos, hbudget⟩ := M47.jointSeed_ball_scale_budget hApos hCpos hrho hvpos
    (show c ≤ 1 / (64 * A * C) from le_rfl) hvsmall
  have hdscale : d ≤ rho ^ 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 32 * A)).mp hyoung
    have hcoeff : 1 ≤ 32 * A := by linarith only [hA]
    exact (by nlinarith only [hcoeff, hd] : d ≤ d * (32 * A)).trans hmul
  have hscale : rho⁻¹ ^ 2 ≤ 1 / d := by
    rw [inv_pow, ← one_div]
    exact one_div_le_one_div_of_le hd hdscale
  have hquot : C * c / v ≤ B / d := by
    calc
      C * c / v ≤ C * c / a := div_le_div_of_nonneg_left (by positivity) ha hv.1
      _ = (C * c / alpha) / d := by dsimp only [a]; ring
      _ ≤ B / d := div_le_div_of_nonneg_right (le_max_right _ _) hd.le
  have hLL0 : L ≤ B / d := max_le
    (hscale.trans (div_le_div_of_nonneg_right hB hd.le)) hquot
  have hbv : b + v ∈ Icc b T := ⟨by linarith only [hvpos],
    by dsimp only [d] at hvd; linarith only [hvd, hbT]⟩
  have hterminal := M47.jointSeed_terminal_below_scale (rho := rho) hC hvpos
    (hnonnegative _ hbv q) hvScalar
  have hearly : Icc b (b + v) ⊆ Icc b T := Icc_subset_Icc le_rfl hbv.2
  let PS : M47ScalarPersistencePredecessors.{u} := {
    tensor_calculus := fun M _ _ _ => P.m04.tensor_calculus 3 M
    scalar_regular := fun M _ _ _ => P.m04.scalar_regular 3 M
    scalar_evolution := fun M _ _ _ => P.m04.scalar_evolution 3 M }
  have hhigh (s : ℝ) (hs : s ∈ Icc b (b + v)) (z : U)
      (hz : L < (G.connection s).scalarCurvature z) :
      M45PointwiseAnalyticEstimate (G.metric s) (G.connection s) z A := by
    have hp : s - T ∈ Icc (b - T) 0 := by
      have hsI := hearly hs
      constructor <;> linarith only [hsI.1, hsI.2]
    have hclock : T + (s - T) / 1 = s := by simp
    have hJ : Icc (T + (s - T) / 1) (b + v) ⊆ Icc b T := by
      rw [hclock]
      exact Icc_subset_Icc hs.1 hbv.2
    have hsOld : s < surgeryEpochStart p.i := by
      have hmid : b + v < T := by dsimp only [d] at hvd; linarith only [hvd, hbT]
      exact (hs.2.trans_lt hmid).trans_le hTold
    have hOld : s ∈ surgeryObservationInterval O ∩ prefixFinalInterval p :=
      ⟨hobs (hearly hs), (hobs (hearly hs)).1, hsOld⟩
    have h := hanalytic F O old (F.slice T) T 1 (Icc (b - T) 0) (Icc b T)
      U hcompact hconnected e (s - T) hp (by simpa only [hclock] using hOld)
      G (b + v) L (by simpa only [hclock] using hs.2) hJ
      (metric (s - T) hp) (scalar (s - T) hp)
      ((congrArg (fun t => ∀ y : U, 0 ≤ (G.connection t).scalarCurvature y)
        hclock).mpr (hnonnegative s (hearly hs)))
      q z hterminal.2 (le_max_left _ _)
      ((congrArg (fun t => L < (G.connection t).scalarCurvature z) hclock).mpr hz)
    exact (congrArg (fun t => M45PointwiseAnalyticEstimate
      (G.metric t) (G.connection t) z A) hclock).mp h
  have hworld := M47.jointSeed_worldline_of_evolution_bound PS G q hbv.1 hearly
    hApos.le hLpos hterminal.1
    (fun s hs hz => (hhigh s (Ioo_subset_Icc_self hs) q hz).2.2)
    (by simpa only [add_sub_cancel_left] using
      hbudget.trans (by norm_num : (1 : ℝ) / 64 ≤ 1 / 4))
  have hRsmall := M47.jointSeed_birth_radius_lt_gradient_radius hA (le_rfl (a := (1 : ℝ)))
    hLpos ha hv.1 hbudget
  have hbirthScalar := M47.jointSeed_scalar_le_on_closure_birth_ball (G.metric b)
    (G.connection b) hApos hLpos q hRsmall.2
    (by linarith only [hworld b ⟨le_rfl, hbv.1⟩, hLpos])
    (fun z hz => (hhigh b ⟨le_rfl, hbv.1⟩ z (by linarith only [hz, hLpos])).2.1)
  have hearlyScalar := M47.jointSeed_early_ball_scalar_bound PS G q hvpos.le hearly hApos.le
    hLpos hbirthScalar (fun z _hz s hs hz =>
      (hhigh s (Ioo_subset_Icc_self hs) z (by linarith only [hz, hLpos])).2.2) hbudget
  have hclockBirth : T - d = b := by dsimp only [d]; ring
  have hwindow : Icc (T - d) T ⊆ Icc b T := by rw [hclockBirth]
  have haccess := M47.jointSeed_mid_age_ball_access P.m04 hd heta
    (hetaA.trans_le hv.1) hvd hA (le_rfl (a := (1 : ℝ))) hLpos ha hv.1
    hwindow hL x path hstart hmin haction hnonnegative
    (by simpa only [hclockBirth] using fun s hs => hsec s (hearly hs))
    (by simpa only [hclockBirth] using fun z hz s hs => (hearlyScalar z hz s hs).le) hbudget
  refine ⟨v, q, hv, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ closure ((G.metric b).ball q (Real.sqrt a / (4 * A * 1))) := by
      simpa only [mul_one] using hz
    calc
      (G.connection b).scalarCurvature z ≤ 4 * L := hbirthScalar z hz'
      _ ≤ 4 * (B / d) := mul_le_mul_of_nonneg_left hLL0 (by norm_num)
      _ = 4 * B / (T - b) := by dsimp only [d]; ring
  · intro z hz s hs
    have hz' : z ∈ closure ((G.metric b).ball q (Real.sqrt a / (4 * A * 1))) := by
      simpa only [mul_one] using hz
    calc
      (G.connection s).scalarCurvature z ≤ 8 * L := (hearlyScalar z hz' s hs).le
      _ ≤ 8 * (B / d) := mul_le_mul_of_nonneg_left hLL0 (by norm_num)
      _ = 8 * B / (T - b) := by dsimp only [d]; ring
  · simpa only [hclockBirth, mul_one] using haccess
  · change 3 * d / 4 ≤ d - v / 2
    linarith only [hvd]
  · change d - v / 2 < d
    linarith only [hvpos]

end PoincareConjecture.Proofs.M47
