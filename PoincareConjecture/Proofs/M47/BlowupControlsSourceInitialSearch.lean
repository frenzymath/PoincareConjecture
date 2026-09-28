import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialFuture
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSearchClock
import PoincareConjecture.Proofs.M47.LimitFinitePreservedBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_source_initial_old_bounded_search
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {m M d L eta : ℝ} (hm : 0 < m) (hd : 0 < d) (hdm : d ≤ m) (hdOne : d ≤ 1)
    (hL : 1 ≤ L) (hmL : 2 / m ≤ L)
    (hShort : 64 * blowupAnalyticConstant S B * L * (2 * d) ≤ 1) (heta : 0 < eta)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q r : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hScale : 64 * (M + 4) ≤ Q) (hLarge : B.curvature_threshold ≤ Q)
    (hThreshold : r⁻¹ ^ 2 ≤ Q) (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (hPinchingScale : blowupPinchingThreshold (4 * L) eta ≤ Q)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (i : Fin (F.event T hT).cap_count) (old : SurgeryTerminalStrongNeck F T hT i)
    (hsmall : F.parameters.delta T ≤ 1 / 200)
    (hage : Q * (base - T) ∈ Icc (0 : ℝ) 1)
    (hmH : m ≤ Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2))
    (hHM : Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) ≤ M)
    {R : ℝ} (hR : 0 < R) :
    let N := ((F.event T hT).necks i).neck
    let q := N.scale⁻¹ ^ 2
    let H := Q / q
    let u := -1 + d / (4 * H)
    let c := H * (u + 1 / 2)
    let shift := -(Q * (base - T)) - H / 2
    let phi := fun s : ℝ => -1 / 2 + s / H
    let V := N.region (-R) R
    ∃ hc : c < 0, ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
      ∃ E : SurgeryFlowCylinder F (F.event T hT).terminal
          (base + shift / Q) Q (Icc b 0) V,
        (∀ s ∈ Icc c 0, phi s ∈ Ioo (-1 : ℝ) 0) ∧
        (∀ s (_hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0)
            (hraw : phi s ∈ Ioo (-1 : ℝ) 0),
          (⟨(base + shift / Q) + s / Q, E.forward s hs'⟩ :
            (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier)) =
            ⟨T + phi s / q, old.cylinder.forward (phi s) hraw⟩) ∧
        (∀ s (hs : s ∈ Icc b c), ∀ x ∈ V,
          (F.connection ((base + shift / Q) + s / Q)).scalarCurvature
            (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x) ≤ 4 * L * Q ∧
          |(F.connection ((base + shift / Q) + s / Q)).curvatureTensorNorm
            (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x)| ≤ (13 * max (4 * L) 1) * Q ∧
          (F.connection ((base + shift / Q) + s / Q)).negativeCurvaturePart
            (E.forward s ⟨hs.1, hs.2.trans hc.le⟩ x) ≤ eta * Q) ∧
        (phi b < -1 - 3 * d / (4 * M) ∨ b ∈ Icc (c - d) c ∧
          (base + shift / Q) + b / Q < T ∧
          ∃ hEvent : (base + shift / Q) + b / Q ∈ F.surgery_times,
            ∀ [Nonempty (F.slice ((base + shift / Q) + b / Q)).carrier],
              ∃ j : Fin (F.event ((base + shift / Q) + b / Q) hEvent).cap_count,
                (E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ '' V ∩
                  ((F.event ((base + shift / Q) + b / Q) hEvent).caps j).carrier).Nonempty) := by
  let N := ((F.event T hT).necks i).neck
  let q := N.scale⁻¹ ^ 2
  let H := Q / q
  let u := -1 + d / (4 * H)
  let c := H * (u + 1 / 2)
  let shift := -(Q * (base - T)) - H / 2
  let phi := fun s : ℝ => -1 / 2 + s / H
  let V := N.region (-R) R
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hH : 0 < H := hm.trans_le hmH
  have hM : 0 < M := hH.trans_le hHM
  have hQ : 0 < Q := (mul_pos hm hq).trans_le ((le_div_iff₀ hq).mp hmH)
  obtain ⟨hu, hu34, _hshift, hbuffer, hlong⟩ :=
    source_initial_search_anchor_bounds hm hd hdm hdOne hmH hHM hage
  have huHalf : u ∈ Ioo (-1 : ℝ) (-1 / 2) :=
    ⟨hu.1, by linarith only [hu34]⟩
  obtain ⟨hc, hV, hne, hraw, e0, hread, hbottom⟩ :=
    exists_source_initial_old_future hT i old hsmall (base := base) hQ huHalf hR
  have hshift : shift ≤ 0 := by
    dsimp only [shift]
    linarith only [hage.1, hH]
  have hsum : shift + c = -(Q * (base - T)) + H * u := by
    dsimp only [shift, c]
    ring
  have hbuffer' : -(M + 3) ≤ shift + c - 2 * d := by
    rw [hsum]
    exact hbuffer
  have h2q : 2 * q ≤ L * Q := by
    have hLm : 2 ≤ L * m := (div_le_iff₀ hm).mp hmL
    have hmQ : m * q ≤ Q := (le_div_iff₀ hq).mp hmH
    have h1 := mul_le_mul_of_nonneg_right hLm hq.le
    have h2 := mul_le_mul_of_nonneg_left hmQ (zero_le_one.trans hL)
    nlinarith only [h1, h2]
  have hTerminal : ∀ x ∈ V,
      (F.connection ((base + shift / Q) + c / Q)).scalarCurvature
        (e0.forward c ⟨le_rfl, hc.le⟩ x) ≤ L * Q :=
    fun x hx => (hbottom _ x hx).trans h2q
  have hScale' : 64 * ((M + 3) + 1) ≤ Q := by linarith only [hScale]
  obtain ⟨b, hb, E, hfuture, hbounds, hstop⟩ :=
    limitFinite_exists_preserved_bounded_search S B p O hInitial hConstants hC
      hBase (by linarith only [hM] : 0 ≤ M + 3) hScale' hLarge hThreshold
      hPinched hEarlier hOverlap P e0 hshift hc.le hd hbuffer' hL hShort
      hV hne hTerminal heta hPinchingScale
  refine ⟨hc, b, hb, E, hraw, ?_, hbounds, ?_⟩
  · intro s hs hs' hsraw
    have heq : E.forward s hs' = e0.forward s hs := funext (hfuture s hs hs')
    rw [heq]
    exact hread s hs hsraw
  · rcases hstop with hstop | ⟨hbshort, hcap⟩
    · left
      change b < c - d at hstop
      have ha : b - c < -d := by linarith only [hstop]
      have hid : phi b = u + (b - c) / H := by
        dsimp only [phi, c]
        field_simp [hH.ne']
        ring
      change phi b < -1 - 3 * d / (4 * M)
      rw [hid]
      exact hlong (b - c) ha
    · refine Or.inr ⟨hbshort, ?_, hcap⟩
      have hclock : (base + shift / Q) + c / Q = T + u / q := by
        dsimp only [shift, c, H]
        field_simp [hQ.ne', hq.ne']
        ring
      have hbq := (div_le_div_iff_of_pos_right hQ).mpr hb.2
      have huq : u / q < 0 := div_neg_of_neg_of_pos hu.2 hq
      linarith only [hclock, hbq, huq]

end PoincareConjecture.M47
