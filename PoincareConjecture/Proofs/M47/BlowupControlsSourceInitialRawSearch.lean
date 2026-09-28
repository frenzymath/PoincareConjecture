import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialLongSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRawPast

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_raw_search
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {m M R : ℝ} (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) :
    ∃ zeta K Q0 : ℝ, 0 < zeta ∧ zeta ≤ 1 / 8 ∧ 0 < K ∧ 0 < Q0 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        O.H ≤ surgeryEpochStart (p.i + 1) →
      ∀ _prior : SurgeryPrefixControls p F O,
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryPostPrefixScales p F O rNext cutoff →
        (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
          F.parameters.delta t ≤ cutoff) →
      ∀ {base Q : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q →
        rNext⁻¹ ^ 2 ≤ Q →
        SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
      ∀ (T : ℝ) (hT : T ∈ F.surgery_times), ∀ [Nonempty (F.slice T).carrier],
      ∀ (i : Fin (F.event T hT).cap_count) (old : SurgeryTerminalStrongNeck F T hT i),
        Q * (base - T) ∈ Icc (0 : ℝ) 1 →
        m ≤ Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) →
        Q / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) ≤ M →
      let N := ((F.event T hT).necks i).neck
      let q := N.scale⁻¹ ^ 2
      ∃ (left : ℝ), left ≤ -1 - 4 * zeta ∧
      ∃ (U : TopologicalSpace.Opens (F.event T hT).terminal.carrier),
        (U : Set (F.event T hT).terminal.carrier) = N.region (-(R + 1)) (R + 1) ∧
        (U : Set (F.event T hT).terminal.carrier).Nonempty ∧
      ∃ D : SurgeryFlowCylinder F (F.event T hT).terminal T q (Icc left (-1 / 2)) U,
        (∀ s (hs : s ∈ Icc left (-1 / 2)) (hs' : s ∈ Ioo (-1 : ℝ) 0),
          ∀ x ∈ U, D.forward s hs x = old.cylinder.forward s hs' x) ∧
        (∀ s (hs : s ∈ Icc left (-1 / 2)), s ∈ Icc (-1 - 4 * zeta) (-1 + zeta) →
          ∀ x ∈ U, (F.connection (T + s / q)).curvatureTensorNorm
            (D.forward s hs x) ≤ K * q) := by
  obtain ⟨L, d, Q0, _hL, _hmL, hd, _hdm, _hdOne, hQ0, search⟩ :=
    exists_source_initial_old_long_search P S B p hp hm hM
      (show 0 < R + 1 by linarith only [hR]) (show (0 : ℝ) < 1 by norm_num)
  let zeta := min (1 / 8) (d / (16 * M))
  let K := (13 * max (4 * L) 1) * M
  have hzeta : 0 < zeta := lt_min (by norm_num) (div_pos hd (by positivity))
  have hzetaSmall : zeta ≤ 1 / 8 := min_le_left _ _
  have hzetaRate : zeta * (16 * M) ≤ d :=
    (le_div_iff₀ (by positivity : 0 < 16 * M)).mp (min_le_right _ _)
  have hK : 0 < K := mul_pos (by positivity) hM
  refine ⟨zeta, K, Q0, hzeta, hzetaSmall, hK, hQ0, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, hsearch⟩ := search rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O hH prior hadmissible hpinched next overlap base Q hBase hLarge hThreshold
    hEarlier T hT hn i old hage hmH hHM
  let N := ((F.event T hT).necks i).neck
  let q := N.scale⁻¹ ^ 2
  let H := Q / q
  let rawAnchor := -1 + d / (4 * H)
  let c := H * (rawAnchor + 1 / 2)
  let shift := -(Q * (base - T)) - H / 2
  let origin := base + shift / Q
  let phi := fun s : ℝ => -1 / 2 + s / H
  let U : TopologicalSpace.Opens (F.event T hT).terminal.carrier :=
    ⟨N.region (-(R + 1)) (R + 1), N.region_isOpen _ _⟩
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hHpos : 0 < H := hm.trans_le hmH
  have hQ : 0 < Q := (mul_pos hm hq).trans_le ((le_div_iff₀ hq).mp hmH)
  have hne : (U : Set (F.event T hT).terminal.carrier).Nonempty := by
    have hcN : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
    have hc0 : (N.coordinate_inverse N.center).2 = 0 :=
      (N.mem_central_sphere_iff_of_mem hcN).mp N.center_on_central_sphere
    refine ⟨N.center, hcN, ?_⟩
    rw [hc0]
    constructor <;> linarith only [hR]
  obtain ⟨hc, b, hb, E, hraw, hfuture, hbounds, hlong⟩ :=
    hsearch F O hH prior hadmissible hpinched next overlap hBase hLarge hThreshold
      hEarlier T hT i old hage hmH hHM
  have hb0 : b ≤ 0 := hb.2.trans hc.le
  have hclock (s : ℝ) : origin + s / Q = T + (-1 / 2 + s / (Q / q)) / q := by
    dsimp only [origin, shift, H]
    field_simp [hQ.ne', hq.ne']
    ring
  have hterminal (x : (F.event T hT).terminal.carrier) (_hx : x ∈ U) :
      (⟨origin + 0 / Q, E.forward 0 ⟨hb0, le_rfl⟩ x⟩ : Σ t, (F.slice t).carrier) =
        ⟨T + (-1 / 2) / q, old.cylinder.forward (-1 / 2) (by norm_num) x⟩ := by
    have h := hfuture 0 ⟨hc.le, le_rfl⟩ ⟨hb0, le_rfl⟩
      (by dsimp only; norm_num)
    have hp := congrArg
      (fun p : (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier) =>
        (⟨p.1, p.2 x⟩ : Σ t, (F.slice t).carrier)) h
    have hphi0 : phi 0 ∈ Ioo (-1 : ℝ) 0 := by
      dsimp only [phi]
      norm_num
    have heval := congrArg
      (fun z : Ioo (-1 : ℝ) 0 =>
        (⟨T + z.val / q, old.cylinder.forward z.val z.property x⟩ :
          Σ t, (F.slice t).carrier))
      (show (⟨phi 0, hphi0⟩ : Ioo (-1 : ℝ) 0) = ⟨-1 / 2, by norm_num⟩ by
        apply Subtype.ext
        simp only [phi, zero_div, add_zero])
    exact (show (⟨origin + 0 / Q, E.forward 0 ⟨hb0, le_rfl⟩ x⟩ :
        Σ t, (F.slice t).carrier) = ⟨T + phi 0 / q,
          old.cylinder.forward (phi 0) hphi0 x⟩ from hp).trans heval
  obtain ⟨hmem, D, hread, hagree⟩ := exists_source_initial_raw_past E old.cylinder hb0
    (fun _ hx => hx.1) hclock hterminal
  let left := -1 / 2 + b / H
  have hleft : left ≤ -1 - 4 * zeta := by
    have hrate : 4 * zeta ≤ 3 * d / (4 * M) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * M)).mpr
      nlinarith only [hzetaRate, hd.le]
    exact hlong.le.trans (by linarith only [hrate])
  refine ⟨left, hleft, U, rfl, hne, D, hagree, ?_⟩
  intro s hs hslab x hx
  let psi := fun v : ℝ => H * (v + 1 / 2)
  have hpsiLower : b ≤ psi s := (hmem hs).1
  have hZetaH : zeta ≤ d / (4 * H) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * H)).mpr
    have hmul := mul_le_mul_of_nonneg_left hHM hzeta.le
    nlinarith only [hmul, hzetaRate, mul_nonneg hzeta.le hM.le]
  have hsAnchor : s ≤ rawAnchor := by
    dsimp only [rawAnchor]
    linarith only [hslab.2, hZetaH]
  have hpsiUpper : psi s ≤ c :=
    mul_le_mul_of_nonneg_left (add_le_add hsAnchor le_rfl) hHpos.le
  have hbnd := hbounds (psi s) ⟨hpsiLower, hpsiUpper⟩ x hx
  have hnorm := congrArg
    (fun p : Σ t, (F.slice t).carrier => (F.connection p.1).curvatureTensorNorm p.2)
    (hread s hs x)
  change (F.connection (T + s / q)).curvatureTensorNorm (D.forward s hs x) =
    (F.connection (origin + psi s / Q)).curvatureTensorNorm
      (E.forward (psi s) (hmem hs) x) at hnorm
  rw [hnorm]
  apply (le_abs_self _).trans (hbnd.2.1.trans ?_)
  have hQle : Q ≤ M * q := (div_le_iff₀ hq).mp hHM
  calc
    (13 * max (4 * L) 1) * Q ≤ (13 * max (4 * L) 1) * (M * q) :=
      mul_le_mul_of_nonneg_left hQle (by positivity)
    _ = K * q := by dsimp only [K]; ring

end PoincareConjecture.M47
