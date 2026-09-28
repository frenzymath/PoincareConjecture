import PoincareConjecture.Proofs.M47.BlowupControlsSourcePointwiseLongCanonical
import PoincareConjecture.Proofs.M36.StandardBalls









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem exists_compact_source_standard_unrestricted_canonical_transfer
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {theta R : ℝ} (htheta : theta < 1) (hR : 0 < R) :
    ∃ A0 eta0 Q0 : ℝ, 0 < A0 ∧ R < A0 ∧ 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧ 0 < Q0 ∧
      ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta b ≤ cutoff) →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
        ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
          (J : Set ℝ)
          (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
            ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
          (initial : SurgeryCapInitialComparison F t hT i A),
          SurgeryCapFamilyComparison F
            (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          0 < F.parameters.h t →
        ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
          ∀ z, S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal R →
          let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
          let x := e.forward s hs (initial.chart z)
          let Q := (F.connection base).scalarCurvature x
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
          SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C := by
  classical
  let K : Set (ℝ × StandardCapSpace) :=
    Icc 0 theta ×ˢ {z | S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal R}
  have hK : IsCompact K := isCompact_Icc.prod
    (M36.standard_closed_ball_compact S.standard_initial hR.le)
  have hlocal (w : K) :=
    exists_source_standard_unrestricted_canonical_neighborhood P S B p hp
      htheta w.property.1 w.val.2
  choose radius accuracy nearTime threshold V hRadius hAccuracy hNearTime hThreshold
    hV hPoint transfer using hlocal
  let cover (w : K) : Set (ℝ × StandardCapSpace) :=
    {s | |s - w.val.1| < nearTime w} ×ˢ V w
  have hCoverOpen (w : K) : IsOpen (cover w) :=
    (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const).prod (hV w)
  have hCover : K ⊆ ⋃ w : K, cover w := by
    intro w hw
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_, hPoint ⟨w, hw⟩⟩
    simpa only [sub_self, abs_zero, mem_ofPred_eq] using hNearTime ⟨w, hw⟩
  obtain ⟨T, hTcover⟩ := hK.elim_finite_subcover cover hCoverOpen hCover
  have hbounds (T : Finset K) :
      ∃ A0 Q0 eta0 : ℝ, 0 < A0 ∧ R < A0 ∧ 0 < Q0 ∧ 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧
        ∀ w ∈ T, radius w ≤ A0 ∧ threshold w ≤ Q0 ∧ eta0 ≤ accuracy w := by
    induction T using Finset.induction with
    | empty =>
        refine ⟨R + 1, 1, 1 / 1000, by linarith, by linarith,
          zero_lt_one, by norm_num, le_rfl, ?_⟩
        simp
    | @insert w T _ ih =>
        obtain ⟨A0, Q0, eta0, hA0, hRA0, hQ0, heta0, hetaSmall, hbound⟩ := ih
        refine ⟨max (radius w) A0, max (threshold w) Q0, min (accuracy w) eta0,
          hA0.trans_le (le_max_right _ _), hRA0.trans_le (le_max_right _ _),
          hQ0.trans_le (le_max_right _ _), lt_min (hAccuracy w) heta0,
          (min_le_right _ _).trans hetaSmall, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ⟨le_max_left _ _, le_max_left _ _, min_le_left _ _⟩
        · obtain ⟨ha, hq, he⟩ := hbound z hz
          exact ⟨ha.trans (le_max_right _ _), hq.trans (le_max_right _ _),
            (min_le_right _ _).trans he⟩
  obtain ⟨A0, Q0, eta0, hA0, hRA0, hQ0, heta0, hetaSmall, hbound⟩ := hbounds T
  refine ⟨A0, eta0, Q0, hA0, hRA0, heta0, hetaSmall, hQ0, ?_⟩
  intro A hA eta heta hetaLe rNext hrNext hrLast
  have hcut (w : T) := transfer w.val A ((hbound w.val w.property).1.trans hA)
    eta heta (hetaLe.trans (hbound w.val w.property).2.2) rNext hrNext hrLast
  choose cutoff hCutoff _hCutoffLast control using hcut
  have hminimum (Z : Finset T) : ∃ d : ℝ, 0 < d ∧ ∀ w ∈ Z, d ≤ cutoff w := by
    induction Z using Finset.induction with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert w Z _ ih =>
        obtain ⟨d, hd, hsmall⟩ := ih
        refine ⟨min (cutoff w) d, lt_min (hCutoff w) hd, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hsmall z hz)
  obtain ⟨d, hd, hsmall⟩ := hminimum Finset.univ
  refine ⟨min (p.Delta (Fin.last p.i)) d,
    lt_min (p.Delta_pos _) hd, min_le_left _ _, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap t hT hn i J e initial comparison
    hzero based hh s hs hst hJ z hz
  dsimp only
  intro hBase hLarge hScale hEarlier
  have hsz : (s, z) ∈ K := ⟨hst, hz⟩
  obtain ⟨w, hwT, hwCover⟩ := mem_iUnion₂.mp (hTcover hsz)
  let wT : T := ⟨w, hwT⟩
  have hcutoff : min (p.Delta (Fin.last p.i)) d ≤ cutoff wT :=
    (min_le_right _ _).trans (hsmall wT (Finset.mem_univ _))
  exact control wT F O hH prior hadmissible hpinch (next.mono_delta hcutoff)
    (fun b hb => (overlap b hb).trans hcutoff) t hT i J e initial comparison hzero
    based hh s hs hst hJ hwCover.1 z hwCover.2 hBase
    ((hbound w hwT).2.1.trans hLarge) hScale hEarlier

end PoincareConjecture.M47
