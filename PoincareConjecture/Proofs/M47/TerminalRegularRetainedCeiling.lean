import PoincareConjecture.Proofs.M47.TerminalRegularSelectedCeiling
import PoincareConjecture.Proofs.M47.TerminalRegularSourceCompactness
import PoincareConjecture.Proofs.M47.SeedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSource_regular_retained_ceiling
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (F : ℕ → SurgeryFlowData.{u}) (O : ∀ n, SurgeryObservation (F n))
    (W : ∀ n, M33RegularHistoryWindow (F n)) (H : ∀ n, M33RegularHistoryData (W n))
    (base r delta : ℕ → ℝ) (ht : ∀ n, base n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (base n)).carrier)
    (old : ∀ n, SurgeryPrefixControls p (F n) (O n))
    (hBase : ∀ n, base n ∈ Ico (surgeryEpochStart p.i) (O n).H)
    (hPinched : ∀ n, SurgeryFlowPinched (F n))
    (hEarlier : ∀ n, SurgeryCanonicalOn (F n) (Ico 0 (base n)) (r n))
    (hFloor : ∀ n, (r n)⁻¹ ^ 2 ≤ ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n)))
    (hOverlap : ∀ n t, t ∈ surgeryObservationInterval (O n) ∩
      Ico (surgeryEpochStart (p.i - 1)) (O n).H → (F n).parameters.delta t ≤ delta n)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hDiverges : Tendsto (fun n => ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n))) atTop atTop)
    (A tau0 K : ℕ → ℝ) (hA : ∀ j, 0 < A j) (htau0 : ∀ j, 0 < tau0 j)
    (hK : ∀ j, 0 ≤ K j) (hcofinal : ∀ a : ℝ, 0 < a → ∃ j, a ≤ A j)
    {rvol vvol : ℝ} (hrvol : 0 < rvol) (hvvol : 0 < vvol) :
    let Q : ℕ → ℝ := fun n => (H n).generalized.scalar ⟨base n, x n⟩
    let center := fun n => (H n).history.forward (base n) (ht n) (x n)
    (∀ᶠ n in atTop, ENNReal.ofReal (vvol / Real.sqrt (Q n) ^ 3) ≤
      calibratedMetricVolume ((H n).generalized.metric (base n))
        (((H n).generalized.metric (base n)).ball (x n) (rvol / Real.sqrt (Q n)))) →
    ∀ alpha : ℕ → ℕ, StrictMono alpha →
    (∀ k j, j ≤ k →
      ∃ e : SurgeryFlowCylinder (F (alpha k)) ((F (alpha k)).slice (base (alpha k)))
        (base (alpha k)) (Q (alpha k)) (Icc (-(tau0 j)) 0)
        (terminalRegularStageSource (F (alpha k)) (base (alpha k)) (Q (alpha k)) (A j)
          (center (alpha k))),
        (∀ hs z, z ∈ terminalRegularStageSource (F (alpha k)) (base (alpha k))
          (Q (alpha k)) (A j) (center (alpha k)) → HEq (e.forward 0 hs z) z) ∧
        ∀ s hs z, z ∈ terminalRegularStageSource (F (alpha k)) (base (alpha k))
          (Q (alpha k)) (A j) (center (alpha k)) →
          ((F (alpha k)).connection (base (alpha k) + s / Q (alpha k))).curvatureTensorNorm
            (e.forward s hs z) ≤ K j * Q (alpha k)) →
    ∃ xi : ℕ → ℕ, StrictMono xi ∧ ∃ K0 : ℝ, 1 ≤ K0 ∧
      (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ∀ z ∈ ((F (alpha (xi k))).metric (base (alpha (xi k)))).ball (center (alpha (xi k)))
            (a / Real.sqrt (Q (alpha (xi k)))),
          ((F (alpha (xi k))).connection (base (alpha (xi k)))).scalarCurvature z ≤
            (2 * K0) * Q (alpha (xi k))) ∧
      ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        IsCompact (closure (((H (alpha (xi k))).generalized.metric (base (alpha (xi k)))).ball
          (x (alpha (xi k))) (a / Real.sqrt (Q (alpha (xi k)))))) := by
  classical
  let Q : ℕ → ℝ := fun n => (H n).generalized.scalar ⟨base n, x n⟩
  let center := fun n => (H n).history.forward (base n) (ht n) (x n)
  dsimp only
  intro hvolume alpha halpha hsource
  choose e hbased hbound using fun j (k : {n : ℕ // j ≤ n}) => hsource k.val j k.property
  have hscale (n : ℕ) : ((F n).connection (base n)).scalarCurvature (center n) = Q n :=
    (H n).scalar_pullback (base n) (ht n) (x n)
  have hQ : Tendsto Q atTop atTop := by
    rw [← show (fun n => ((F n).connection (base n)).scalarCurvature (center n)) = Q from
      funext hscale]
    exact hDiverges
  have hPositive (k : ℕ) : 0 < ((F (alpha k)).connection (base (alpha k))).scalarCurvature
      (center (alpha k)) := by
    rw [hscale]
    exact (e 0 ⟨k, Nat.zero_le k⟩).scale_pos
  have hstrictCofinal (a : ℝ) (ha : 0 < a) : ∃ j, a < A j := by
    obtain ⟨j, hj⟩ := hcofinal (a + 1) (by linarith)
    exact ⟨j, by linarith⟩
  have hcompact := terminalSource_blowup_base_balls_compact
    (fun k => F (alpha k)) (fun k => W (alpha k)) (fun k => H (alpha k))
    (base ∘ alpha) (fun k => ht (alpha k)) (fun k => x (alpha k))
    hPositive (hDiverges.comp halpha.tendsto_atTop) A tau0 htau0 hstrictCofinal
    (fun j => by
      filter_upwards [eventually_ge_atTop j] with k hjk
      exact ⟨e j ⟨k, hjk⟩, hbased j ⟨k, hjk⟩⟩)
  obtain ⟨m, hm, rho, hparams, hsmall, lambda, hlambda, _available, data, _hsame⟩ :=
    terminalSource_regular_stage_family P S B p hp
      (fun k => F (alpha k)) (fun k => O (alpha k))
      (fun k => W (alpha k)) (fun k => H (alpha k))
      (base ∘ alpha) (r ∘ alpha) (delta ∘ alpha) (fun k => ht (alpha k))
      (fun k => x (alpha k)) (fun k => old (alpha k)) (fun k => hBase (alpha k))
      (fun k => hPinched (alpha k)) (fun k => hEarlier (alpha k))
      (fun k => hFloor (alpha k)) (fun k => hOverlap (alpha k))
      (hdelta.comp halpha.tendsto_atTop) (hDiverges.comp halpha.tendsto_atTop)
      A tau0 K hA htau0 hK hcofinal hrvol hvvol
      (halpha.tendsto_atTop.eventually hvolume) e hbased hbound
  let a := fun j : ℕ => (j : ℝ) + 1
  let Rbig := fun j => a j + rvol + 1
  let L := fun j => max 1 (9 * K (m j))
  let tau := fun j => min (tau0 (m j) / 2) (1 / (4 * blowupAnalyticConstant S B * L j))
  let Hbar := fun j => 13 * max (4 * L j / 3) 1
  let R := fun j => RiemannianMetric.localInjectivityRadius 3 (Hbar j) (Rbig j) vvol
  let N := fun j => ⌈RiemannianMetric.modelVolume 3 (Hbar j) (3 * a j) /
    RiemannianMetric.modelVolume 3 (Hbar j) (min (a j / 2) (rho j / 4) / 2)⌉₊ + 1
  let raw := alpha ∘ lambda
  have hraw : StrictMono raw := halpha.comp hlambda
  have hAselected (s : ℝ) (_hs : 0 < s) : ∃ j, s ≤ A (m j) := by
    obtain ⟨j, hj⟩ := exists_nat_ge s
    refine ⟨j, ?_⟩
    have hb := hm j
    dsimp only at hb
    nlinarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
  have hfloor (k : ℕ) : (r (raw k))⁻¹ ^ 2 ≤ Q (raw k) := by
    rw [← hscale]
    exact hFloor (raw k)
  have hepsilon (k : ℕ) : (F (raw k)).parameters.epsilon = S.setup.epsilon := by
    rw [(old (raw k)).epsilon_eq, hp.setup_eq]
  have hC (k : ℕ) : (F (raw k)).parameters.C = S.setup.C := by
    rw [(old (raw k)).C_eq, hp.setup_eq]
  obtain ⟨beta, hbeta, K0, hK0, hceiling⟩ := terminalSource_regular_selected_ceiling
    S B p (fun k => F (raw k)) (fun k => O (raw k))
    (fun k => W (raw k)) (fun k => H (raw k))
    (base ∘ raw) (Q ∘ raw) (r ∘ raw) (A ∘ m) (tau0 ∘ m)
    tau (K ∘ m) L R rho N (fun k => center (raw k)) data
    (fun j => (hparams j).2.2.1) P.toM46
    (fun j => (hparams j).1) (fun j => (hparams j).2.2.2.1) hsmall
    (hQ.comp hraw.tendsto_atTop) hAselected hfloor hepsilon hC (fun k => hEarlier (raw k))
  refine ⟨lambda ∘ beta, hlambda.comp hbeta, K0, hK0, hceiling, ?_⟩
  intro a ha
  exact (hlambda.comp hbeta).tendsto_atTop.eventually (hcompact a ha)

end PoincareConjecture.M47
