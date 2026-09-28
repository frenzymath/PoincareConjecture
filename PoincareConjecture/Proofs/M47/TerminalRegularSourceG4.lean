import PoincareConjecture.Proofs.M47.TerminalRegularSourceRealization
import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4Assembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalSource_regular_stage_G4
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {α : Type v} (l : Filter α)
    (F : α → SurgeryFlowData.{u}) (O : ∀ k, SurgeryObservation (F k))
    (W : ∀ k, M33RegularHistoryWindow (F k)) (H : ∀ k, M33RegularHistoryData (W k))
    (base r delta : α → ℝ) (ht : ∀ k, base k ∈ (H k).generalized.interval)
    (x : ∀ k, ((H k).generalized.slice (base k)).carrier)
    (old : ∀ k, SurgeryPrefixControls p (F k) (O k))
    (hBase : ∀ k, base k ∈ Ico (surgeryEpochStart p.i) (O k).H)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (base k)) (r k))
    (hFloor : ∀ k, (r k)⁻¹ ^ 2 ≤ ((F k).connection (base k)).scalarCurvature
      ((H k).history.forward (base k) (ht k) (x k)))
    (hOverlap : ∀ k t, t ∈ surgeryObservationInterval (O k) ∩
      Ico (surgeryEpochStart (p.i - 1)) (O k).H → (F k).parameters.delta t ≤ delta k)
    (hdelta : Tendsto delta l (𝓝 0))
    (hDiverges : Tendsto (fun k => ((F k).connection (base k)).scalarCurvature
      ((H k).history.forward (base k) (ht k) (x k))) l atTop)
    {A tau0 K : ℝ} (hA : 0 < A) (htau0 : 0 < tau0) :
    let Q : α → ℝ := fun k => (H k).generalized.scalar ⟨base k, x k⟩
    let U : ∀ k, TopologicalSpace.Opens ((F k).slice (base k)).carrier := fun k =>
      ⟨((F k).metric (base k)).ball ((H k).history.forward (base k) (ht k) (x k))
        (A / Real.sqrt (Q k)), M04.initial_ball_isOpen _ _ _⟩
    let L : ℝ := max 1 (9 * K)
    let tau : ℝ := min (tau0 / 2) (1 / (4 * blowupAnalyticConstant S B * L))
    0 < tau ∧ tau < tau0 ∧ 1 ≤ L ∧
    ∀ e : ∀ k, SurgeryFlowCylinder (F k) ((F k).slice (base k)) (base k) (Q k)
      (Icc (-tau0) 0) (U k),
    (∀ k hs y, y ∈ U k → HEq ((e k).forward 0 hs y) y) →
    (∀ k s hs y, y ∈ U k → ((F k).connection (base k + s / Q k)).curvatureTensorNorm
      ((e k).forward s hs y) ≤ K * Q k) →
    ∃ p0 : ∀ k, U k,
    ∃ htime : ∀ k s, s ∈ Icc (-tau) 0 → base k + s / Q k ∈ (H k).generalized.interval,
    ∃ d : ∀ k, GeneralizedFlowCylinder (H k).generalized ((F k).slice (base k))
      (base k) (Q k) (Icc (-tau) 0) (U k),
    ∃ G : ∀ k, RicciFlow 3 (U k) (Icc (-tau) 0),
      (∀ k, (p0 k).val = (H k).history.forward (base k) (ht k) (x k) ∧
        (∀ s hs y, y ∈ U k → (H k).history.forward (base k + s / Q k) (htime k s hs)
          ((d k).forward s hs y) = (e k).forward s
            ⟨(neg_le_neg (show tau ≤ tau0 from
              (min_le_left _ _).trans (by linarith))).trans hs.1, hs.2⟩ y) ∧
        (∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (z : U k),
          (∀ v w : TangentSpace (𝓡 3) z,
            ((G k).metric s).inner z v w = (d k).pullbackInner s hs z.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U k → ((F k).slice (base k)).carrier) z v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U k → ((F k).slice (base k)).carrier) z w)) ∧
          ((G k).connection s).scalarCurvature z =
            ((H k).generalized.connection (base k + s / Q k)).scalarCurvature
              ((d k).forward s hs z.val) / Q k ∧
          ((G k).connection s).curvatureTensorNorm z =
            ((H k).generalized.connection (base k + s / Q k)).curvatureTensorNorm
              ((d k).forward s hs z.val) / Q k) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : U k, ((G k).connection s).curvatureTensorNorm z ≤ K) ∧
        (∀ z : U k, ((G k).connection 0).scalarCurvature z =
          ((F k).connection (base k)).scalarCurvature z.val / Q k) ∧
        ((G k).connection 0).scalarCurvature (p0 k) = 1 ∧
        (∀ y, y ∈ U k → normalizedCylinderScalar (d k) y 0 ≤ L) ∧
        let h0 : (0 : ℝ) ∈ Icc (-tau) 0 :=
          ⟨neg_nonpos.mpr (by dsimp only [tau, L, blowupAnalyticConstant]; positivity), le_rfl⟩
        let j := terminalSourceNormal_terminalMap (U k) (p0 k)
          (terminalSourceNormal_historyCylinder (H k) (U k) (htime k) (d k)) h0
        j.source = univ ∧ j.target = U k ∧ (∀ z : U k, j z = z.val)) ∧
      ∀ᶠ k in l, ∀ R : ℝ, ∀ C : TerminalSourceChart ((G k).metric 0) R,
        TerminalSourceJetsG4Good S B p (O k) (H k) (U k) (d k) (G k)
          (rNext := r k) (L := L) (eta := 1) C := by
  classical
  let Q : α → ℝ := fun k => (H k).generalized.scalar ⟨base k, x k⟩
  let U : ∀ k, TopologicalSpace.Opens ((F k).slice (base k)).carrier := fun k =>
    ⟨((F k).metric (base k)).ball ((H k).history.forward (base k) (ht k) (x k))
      (A / Real.sqrt (Q k)), M04.initial_ball_isOpen _ _ _⟩
  let L : ℝ := max 1 (9 * K)
  let tau : ℝ := min (tau0 / 2) (1 / (4 * blowupAnalyticConstant S B * L))
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hden : 0 < 4 * blowupAnalyticConstant S B * L :=
    mul_pos (mul_pos (by norm_num) (blowupAnalyticConstant_pos S B)) hLpos
  have htau : 0 < tau := lt_min (half_pos htau0) (one_div_pos.mpr hden)
  have htt : tau < tau0 := (min_le_left _ _).trans_lt (half_lt_self htau0)
  have hshort : blowupAnalyticConstant S B * L * tau ≤ 1 / 4 := by
    have h := (le_div_iff₀ hden).mp (min_le_right (tau0 / 2)
      (1 / (4 * blowupAnalyticConstant S B * L)))
    dsimp only [tau]
    nlinarith
  refine ⟨htau, htt, hL, ?_⟩
  intro e hbased hbound
  choose p0 hp0 htime d G hmaps _hmetric hG _hphysical hnorm hscalar hone hterminal hmap
    using fun k => terminalSource_realize_regular_stage (H k) (ht k) (x k)
      P hA htau htt (e k) (hbased k) (hbound k)
  have hterminalL (k : α) (y : ((F k).slice (base k)).carrier) (hy : y ∈ U k) :
      normalizedCylinderScalar (d k) y 0 ≤ L :=
    (hterminal k y hy).trans (le_max_right _ _)
  refine ⟨p0, htime, d, G, ?_, ?_⟩
  · intro k
    exact ⟨hp0 k, hmaps k, hG k, hnorm k, hscalar k, hone k, hterminalL k, hmap k⟩
  · have hscale (k : α) : ((F k).connection (base k)).scalarCurvature
        ((H k).history.forward (base k) (ht k) (x k)) = Q k :=
      (H k).scalar_pullback (base k) (ht k) (x k)
    have hQ : Tendsto Q l atTop := by
      simpa only [hscale] using hDiverges
    have hdeltaSmall : ∀ᶠ k in l, delta k ≤ B.delta S.setup.standard_initial S.constants :=
      hdelta.eventually (eventually_le_nhds (B.delta_pos _ _))
    filter_upwards [hQ.eventually (eventually_ge_atTop (64 * (tau + 1))),
      hQ.eventually (eventually_ge_atTop B.curvature_threshold),
      hQ.eventually (eventually_ge_atTop (blowupPinchingThreshold (4 * L / 3) 1)),
      hdeltaSmall] with k hscale64 hlarge hpinchingScale hdeltaK
    intro R C
    exact {
      hInitial := by rw [(old k).standard_initial_eq, hp.setup_eq]
      hConstants := (old k).local_constants_eq
      hC := by rw [(old k).C_eq, hp.setup_eq]
      hBase := hBase k
      hTauNonneg := htau.le
      hScale := hscale64
      hLarge := hlarge
      hThreshold := by simpa only [hscale] using hFloor k
      hPinched := hPinched k
      hEarlier := fun s hs hsF y hy => hEarlier k s ⟨hs.1.1, hs.2⟩ hsF y hy
      hOverlap := fun s hs => (hOverlap k s hs).trans hdeltaK
      hne := ⟨p0 k, (p0 k).property⟩
      htime := htime k
      hnorm := fun s hs z => (hG k s hs z).2.2
      hL := hL
      hTerminal := hterminalL k
      hShort := hshort
      heta := zero_lt_one
      hPinchingScale := hpinchingScale }

end PoincareConjecture.M47
