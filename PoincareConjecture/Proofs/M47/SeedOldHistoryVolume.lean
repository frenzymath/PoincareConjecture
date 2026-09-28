import PoincareConjecture.Proofs.M47.SeedOldHistoryAnalytics
import PoincareConjecture.Proofs.M47.SeedUniformOrdinaryVolume
import PoincareConjecture.Proofs.M47.JointSeedPoint
import PoincareConjecture.Proofs.M47.JointSeedBallScales
import PoincareConjecture.Proofs.M47.JointSeedBallAccess
import PoincareConjecture.Proofs.M47.SeedM15Physical









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_old_history_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {g0 : ℝ} (hg0 : 0 < g0) :
    ∃ k : ℝ, 0 < k ∧ ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryPrefixControls p F O → SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      ∀ (T a0 : ℝ), T ≤ O.H → T ≤ surgeryEpochStart (p.i + 1) →
        g0 ≤ -a0 → T + a0 ≤ surgeryEpochStart p.i - g0 →
        ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
          IsCompact (U : Set (F.slice T).carrier) → IsConnected (U : Set (F.slice T).carrier) →
          ∀ (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a0 0) U),
            (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
            ∀ G : RicciFlow 3 U (Icc (T + a0) T),
              (∀ s (hs : s ∈ Icc a0 0) (y : U) (v w : TangentSpace (𝓡 3) y),
                (F.metric (T + s / 1)).inner (e.forward s hs y.val)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                    (G.metric (T + s / 1)).inner y v w) →
              (∀ s (hs : s ∈ Icc a0 0) (y : U),
                (G.connection (T + s / 1)).scalarCurvature y =
                  (F.connection (T + s / 1)).scalarCurvature (e.forward s hs y.val)) →
              (∀ s (hs : s ∈ Icc a0 0) (y : U),
                (G.connection (T + s / 1)).curvatureTensorNorm y =
                  (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y.val)) →
              (∀ t ∈ Icc (T + a0) T, ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
                0 ≤ (G.connection t).curvatureTensor y v w v w) →
              (∀ (ha0 : a0 ∈ Icc a0 0) (q : U), T + a0 / 1 = 0 ∨
                ¬ SurgeryPositiveComponentAt F (T + a0 / 1) (e.forward a0 ha0 q.val) ∨
                ∃ hT : T + a0 / 1 ∈ F.surgery_times,
                  ∀ [Nonempty (F.slice (T + a0 / 1)).carrier],
                    ∃ i : Fin (F.event (T + a0 / 1) hT).cap_count,
                      (connectedComponent (e.forward a0 ha0 q.val) ∩
                        ((F.event (T + a0 / 1) hT).caps i).carrier).Nonempty) →
              ∀ (x : U) (r : ℝ), 0 < r → r ≤ p.setup.epsilon →
                ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                  ((F.metric T).ball x.val r),
                  (∀ hs y, y ∈ (F.metric T).ball x.val r → HEq (test.forward 0 hs y) y) →
                  (∀ s (hs : s ∈ Icc (-r ^ 2) 0), ∀ y ∈ (F.metric T).ball x.val r,
                    (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤
                      r⁻¹ ^ 2) →
                  ENNReal.ofReal (k * r ^ 3) ≤
                    calibratedMetricVolume (F.metric T) ((F.metric T).ball x.val r) := by
  obtain ⟨A, hA, _hCA, hanalytic⟩ := exists_seed_old_history_analytic_bound P S p compatible
  let C := S.setup.C
  let rho := p.r (Fin.last p.i)
  have hC : 1 ≤ C := S.setup.C_large
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hrho : 0 < rho := p.r_pos _
  let sigma := min (g0 / 2) (rho ^ 2 / (64 * A))
  let c := 1 / (64 * A * C)
  let a := sigma * Real.exp (-5 / c)
  let eta := a / 2
  let R := Real.sqrt a / (4 * A * 1)
  let L0 := max (rho⁻¹ ^ 2) (C * c / a)
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have ha : 0 < a := mul_pos hsigma (Real.exp_pos _)
  have heta : 0 < eta := half_pos ha
  have hetaA : eta < a := half_lt_self ha
  have hR : 0 < R := by dsimp only [R]; positivity
  have hL0 : 0 < L0 := (sq_pos_of_pos (inv_pos.mpr hrho)).trans_le (le_max_left _ _)
  obtain ⟨V, hV, hvolume⟩ := exists_uniform_ordinary_birth_volume P S p compatible
    (show 0 < 2 * L0 by positivity)
    (show (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ 2 * L0 from
      (le_max_left _ _).trans (by linarith only [hL0])) hR
  let taubar := surgeryEpochStart (p.i + 1)
  let age := 3 * g0 / 4
  have hage : 0 < age := by dsimp only [age]; positivity
  obtain ⟨Q⟩ := P.m15.uniform taubar 2 (V / 8)
    (by dsimp only [taubar, surgeryEpochStart]; positivity) (by norm_num) (by positivity)
  refine ⟨Q.kappa * seedRadiusFactor p.setup.epsilon age ^ 3,
    seedRadiusFactor_volume_constant_pos p.setup.epsilon_pos hage Q.kappa_pos, ?_⟩
  intro F O old hpinch hpolicy T a0 hTH hTmax hage0 hbirthOld U hcompact hconnected
    e based G metric scalar norm hsec hbirth x r hr hrepsilon test testBased testCurv
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  let b := T + a0
  let d := T - b
  have ha0 : a0 < 0 := by linarith only [hage0, hg0]
  have hbT : b < T := by dsimp only [b]; linarith only [ha0]
  have hd : 0 < d := sub_pos.mpr hbT
  have hdg : g0 ≤ d := by dsimp only [d, b]; linarith only [hage0]
  have hb0 : 0 ≤ b := by
    have ht := e.time_subset (mem_image_of_mem (fun s : ℝ => T + s / 1)
      (show a0 ∈ Icc a0 0 from ⟨le_rfl, ha0.le⟩))
    simpa only [div_one, mem_Ici, b] using F.time_domain_nonnegative ht
  have hnonnegative : ∀ s ∈ Icc b T, ∀ y : U, 0 ≤ (G.connection s).scalarCurvature y :=
    fun s hs y => M04.nonneg_scalar_of_nonnegativeSectionalAt (G.connection s) y (hsec s hs y)
  have hsigmaAge : sigma ≤ (T - b) / 2 := (min_le_left _ _).trans
    (by change g0 / 2 ≤ d / 2; linarith only [hdg])
  obtain ⟨hL, path, hstart, hmin, haction, v, hv, hvScalar, _hvBound, _hred⟩ :=
    M47.exists_jointSeed_point P.ordinary hbT hc hsigma hsigmaAge rfl heta hetaA G hnonnegative x
  let q := path.curve (d - v)
  have hvpos : 0 < v := ha.trans_le hv.1
  have hvsigma : v ≤ sigma := hv.2
  have hvd : v ≤ d / 2 := hvsigma.trans hsigmaAge
  have hvsmall : v ≤ rho ^ 2 / (64 * A) := hvsigma.trans (min_le_right _ _)
  let L := max (rho⁻¹ ^ 2) (C * c / v)
  obtain ⟨hLpos, hbudget⟩ := M47.jointSeed_ball_scale_budget hApos hCpos hrho hvpos
    (show c ≤ 1 / (64 * A * C) from le_rfl) hvsmall
  have hLL0 : L ≤ L0 := max_le_max le_rfl
    (div_le_div_of_nonneg_left (mul_nonneg hCpos.le hc.le) ha hv.1)
  have hbv : b + v ∈ Icc b T := ⟨by linarith only [hvpos],
    by dsimp only [d] at hvd; linarith only [hvd, hbT]⟩
  have hterminal := M47.jointSeed_terminal_below_scale (rho := rho) hC hvpos
    (hnonnegative _ hbv q) hvScalar
  have hearly : Icc b (b + v) ⊆ Icc b T := Icc_subset_Icc le_rfl hbv.2
  have hOld : Icc b (b + v) ⊆ surgeryObservationInterval O ∩ prefixFinalInterval p := by
    intro s hs
    have hvg : v ≤ g0 / 2 := hvsigma.trans (min_le_left _ _)
    have hsOld : s < surgeryEpochStart p.i := by
      dsimp only [b] at hs
      linarith only [hs.2, hvg, hbirthOld, hg0]
    have hsT : s < T := by
      dsimp only [d] at hvd
      linarith only [hs.2, hvd, hbT]
    exact ⟨⟨hb0.trans hs.1, hsT.trans_le hTH⟩, hb0.trans hs.1, hsOld⟩
  let PS : M47ScalarPersistencePredecessors.{u} := {
    tensor_calculus := fun M _ _ _ => P.m04.tensor_calculus 3 M
    scalar_regular := fun M _ _ _ => P.m04.scalar_regular 3 M
    scalar_evolution := fun M _ _ _ => P.m04.scalar_evolution 3 M }
  have hhigh (s : ℝ) (hs : s ∈ Icc b (b + v)) (z : U)
      (hz : L < (G.connection s).scalarCurvature z) :
      M45PointwiseAnalyticEstimate (G.metric s) (G.connection s) z A := by
    have hp : s - T ∈ Icc a0 0 := by
      have hsI := hearly hs
      dsimp only [b] at hsI
      constructor <;> linarith only [hsI.1, hsI.2]
    have hclock : T + (s - T) / 1 = s := by simp
    have hJ : Icc (T + (s - T) / 1) (b + v) ⊆ Icc b T := by
      rw [hclock]
      exact Icc_subset_Icc hs.1 hbv.2
    have h := hanalytic F O old (F.slice T) T 1 (Icc a0 0) (Icc b T)
      U hcompact hconnected e (s - T) hp (by simpa only [hclock] using hOld hs)
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
  have hbaseParam : a0 ∈ Icc a0 0 := ⟨le_rfl, ha0.le⟩
  have hclockBase : T + a0 / 1 = b := by simp only [div_one, b]
  have hbirthTime : T + a0 / 1 ∈ surgeryObservationInterval O ∩ prefixFinalInterval p := by
    simpa only [div_one] using hOld (show b ∈ Icc b (b + v) from ⟨le_rfl, hbv.1⟩)
  have hvol := hvolume F O old hpinch hpolicy (F.slice T) T 1 (Icc a0 0)
    U hcompact hconnected e a0 hbaseParam hbirthTime
    (G.metric (T + a0 / 1)) (G.connection (T + a0 / 1))
    (fun y w z => (metric a0 hbaseParam y w z).symm) (scalar a0 hbaseParam)
    ((congrArg (fun t => ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      0 ≤ (G.connection t).curvatureTensor y v w v w) hclockBase).mpr
        (hsec b ⟨le_rfl, hbT.le⟩)) q
    (by
      intro z hz
      have hz' : z ∈ closure ((G.metric b).ball q R) := by
        exact subset_closure (by simpa only [div_one] using hz)
      have h := hbirthScalar z hz'
      have hbound : (G.connection b).scalarCurvature z ≤ 2 * (2 * L0) := by
        linarith only [h, hLL0]
      exact (congrArg (fun t => (G.connection t).scalarCurvature z ≤ 2 * (2 * L0))
        hclockBase).mpr hbound)
    (hbirth hbaseParam q)
  have hbirthVolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.metric b) ((G.metric b).ball q (R / 2)) := by
    simpa only [div_one] using hvol
  have hmidVolume := seed_midpoint_volume_of_birth_floor G q hR hA hLpos hvpos.le hearly
    (fun s hs => hsec s (hearly hs)) (fun z hz s hs => (hearlyScalar z hz s hs).le)
    hbudget hbirthVolume
  have hclockBirth : T - d = b := by dsimp only [d]; ring
  have hwindow : Icc (T - d) T ⊆ Icc b T := by rw [hclockBirth]
  have haccess := M47.jointSeed_mid_age_ball_access P.m04 hd heta
    (hetaA.trans_le hv.1) hvd hA (le_rfl (a := (1 : ℝ))) hLpos ha hv.1
    hwindow hL x path hstart hmin haction hnonnegative
    (by simpa only [hclockBirth] using fun s hs => hsec s (hearly hs))
    (by simpa only [hclockBirth] using fun z hz s hs => (hearlyScalar z hz s hs).le) hbudget
  let seed := (G.metric (b + v / 2)).ball q (R / 2)
  have hopen : IsOpen seed := M04.initial_ball_isOpen _ _ _
  have hseedAccess : ∀ y ∈ seed, reducedLength G T x y (d - v / 2) ≤ 2 := by
    simpa only [hclockBirth] using haccess
  have hclockMid : T - (d - v / 2) = b + v / 2 := by dsimp only [d]; ring
  apply M47.seedM15_physical_volume (tau := d - v / 2)
    P.m12 P.m13 P.m14 P.ordinary Q p.setup.epsilon_pos hage
    ha0 U e based G metric norm x (by dsimp only [d, b]; linarith only [hvpos])
    (by dsimp only [taubar, d]; linarith only [hTmax, hb0, hvpos])
    (by dsimp only [age]; linarith only [hdg, hvd]) seed hopen hseedAccess
    (by simpa only [hclockMid] using hmidVolume) hr hrepsilon test testBased testCurv

end PoincareConjecture.Proofs.M47
