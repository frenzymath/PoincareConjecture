import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.VaryingTraceCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.WeakCompactness Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem bounded_columns_subsequence
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e)
    (R : E →L[ℝ] LoopPlane) (c0 c1 : ℝ → M) (hc0 : Continuous c0) (hc1 : Continuous c1)
    (H0 H1 : ℝ ≃o ℝ) {frequency D : ℝ} (hf : frequency ≠ 0)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (A : ℕ → M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D)
    {C : ℝ} (hC : ∀ j i, ‖(A j).annulus.column i‖ ^ 2 ≤ C) :
    ∃ (s : ℕ → ℕ) (L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D),
      StrictMono s ∧
      Tendsto (fun j => (A (s j)).annulus.value) atTop (𝓝 L.annulus.value) ∧
      (∀ i, WeakConverges (fun j => (A (s j)).annulus.column i) (L.annulus.column i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => (A (s j)).annulus.map p) atTop (𝓝 (L.annulus.map p))) ∧
      WeakConverges (fun j => (A (s j)).phase) L.phase ∧
      (∀ i, WeakConverges (fun j => (A (s j)).phaseColumn i) (L.phaseColumn i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => (A (s j)).phase p) atTop (𝓝 (L.phase p))) ∧
      (∀ x, Tendsto (fun j => (A (s j)).label0 x) atTop (𝓝 (L.label0 x))) ∧
      (∀ x, Tendsto (fun j => (A (s j)).label1 x) atTop (𝓝 (L.label1 x))) ∧
      Tendsto (fun j => (A (s j)).offset) atTop (𝓝 L.offset) := by
  classical
  let b0 := fun j x => H0 ((A j).label0 x)
  let b1 := fun j x => H1 ((A j).label1 x) + (A j).offset
  let B0 := max |H0 0| |H0 curvePeriod|
  let B1 := max |H1 0| |H1 curvePeriod|
  let Cphase := (‖R‖ ^ 2 / frequency ^ 2) * C
  have hnormalize (H : ℝ ≃o ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      |H x| ≤ max |H 0| |H curvePeriod| := by
    have hlo := H.monotone hx.1
    have hhi := H.monotone hx.2
    have ha := abs_le.mp (le_max_left |H 0| |H curvePeriod|)
    have hb := abs_le.mp (le_max_right |H 0| |H curvePeriod|)
    rw [abs_le]
    constructor <;> linarith
  have hb0 (j : ℕ) : |b0 j 0| ≤ B0 := hnormalize H0 (A j).label0_normalized
  have hp0 (j : ℕ) (x : ℝ) : b0 j (x + curvePeriod) = b0 j x + D := by
    dsimp only [b0]
    rw [(A j).label0_period, hH0]
  have hp1 (j : ℕ) (x : ℝ) : b1 j (x + curvePeriod) = b1 j x + D := by
    dsimp only [b1]
    rw [(A j).label1_period, hH1]
    ring
  have hm0 (j : ℕ) : Monotone (b0 j) := H0.monotone.comp (A j).label0_monotone
  have hm1 (j : ℕ) : Monotone (b1 j) :=
    (H1.monotone.comp (A j).label1_monotone).add_const _
  have hphaseC (j : ℕ) (i : Fin 2) : (∫ p in S, ((A j).phaseColumn i p) ^ 2) ≤ Cphase :=
    ((A j).annulus.real_phase_column_integral_le_norm_sq R hf (Lp.memLp (A j).phase)
      (fun i => Lp.memLp ((A j).phaseColumn i)) (A j).phase_weak (A j).phase_observation i).trans
      (mul_le_mul_of_nonneg_left (hC j i) (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  obtain ⟨s0, U, W, l0, l1, hs0, hU, hW, ha, hw, hl0, hcl0, hl1, hcl1,
      hpl0, hpl1, -, ht0, ht1, hseam, hgreen⟩ :=
    m64WeakPhase_monotone_two_real_traces_subsequence
      (fun j => (A j).phase) (fun j i => (A j).phaseColumn i) b0 b1
      (fun j => Lp.memLp (A j).phase) (fun j i => Lp.memLp ((A j).phaseColumn i))
      (fun j => (A j).phase_weak) hm0 hm1 hp0 hp1 hb0 hphaseC
      (fun j => (A j).phase_seam) (fun j => (A j).phase_boundary)
  simp only [Lp.toLp_coeFn] at hU hW
  let Boffset := B0 + |D| + (volume.real S + Cphase) / (2 * curvePeriod) + B1
  have hoffset (j : ℕ) : (A j).offset ∈ Icc (-Boffset) Boffset := by
    have hupper := m64WeakPhase_upper_zero_bound (A j).phase ((A j).phaseColumn 1)
      (b0 j) (b1 j) (Lp.memLp ((A j).phaseColumn 1)) (hm0 j) (hm1 j)
      (hp0 j) (hp1 j) (hb0 j) (hphaseC j 1) (A j).phase_boundary
    apply abs_le.mp
    calc
      |(A j).offset| = |b1 j 0 - H1 ((A j).label1 0)| := by simp only [b1, add_sub_cancel_left]
      _ ≤ |b1 j 0| + |H1 ((A j).label1 0)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (b1 j 0) 0 (H1 ((A j).label1 0))
      _ ≤ Boffset := add_le_add hupper (hnormalize H1 (A j).label1_normalized)
  obtain ⟨delta, -, s1, hs1, hdelta⟩ := isCompact_Icc.tendsto_subseq (fun j => hoffset (s0 j))
  let t := s0 ∘ s1
  let sigma0 := fun x => H0.symm (l0 x)
  let sigma1 := fun x => H1.symm (l1 x - delta)
  have htrace0 (x : ℝ) : H0 (sigma0 x) = l0 x := H0.apply_symm_apply _
  have htrace1 (x : ℝ) : H1 (sigma1 x) + delta = l1 x := by
    rw [H1.apply_symm_apply]
    exact sub_add_cancel _ _
  have hlabel0 (x : ℝ) : Tendsto (fun j => (A (t j)).label0 x) atTop (𝓝 (sigma0 x)) := by
    have hh := (H0.symm.continuous.tendsto (l0 x)).comp ((ht0 x).comp hs1.tendsto_atTop)
    simpa only [Function.comp_def, b0, OrderIso.symm_apply_apply, t, sigma0] using hh
  have hlabel1 (x : ℝ) : Tendsto (fun j => (A (t j)).label1 x) atTop (𝓝 (sigma1 x)) := by
    have hh := (H1.symm.continuous.tendsto (l1 x - delta)).comp
      (((ht1 x).comp hs1.tendsto_atTop).sub hdelta)
    simpa only [Function.comp_def, b1, add_sub_cancel_right, OrderIso.symm_apply_apply,
      t, sigma1] using hh
  have hmono0 : Monotone sigma0 := H0.symm.monotone.comp hl0
  have hmono1 : Monotone sigma1 := H1.symm.monotone.comp
    (fun _ _ h => sub_le_sub_right (hl1 h) delta)
  have hperiod0 (x : ℝ) : sigma0 (x + curvePeriod) = sigma0 x + curvePeriod := by
    apply H0.injective
    rw [htrace0, hH0, htrace0, hpl0]
  have hperiod1 (x : ℝ) : sigma1 (x + curvePeriod) = sigma1 x + curvePeriod := by
    apply H1.injective
    have h0 := htrace1 x
    have h1 := htrace1 (x + curvePeriod)
    rw [hH1, hpl1] at *
    linarith
  have hnorm0 : sigma0 0 ∈ Icc (0 : ℝ) curvePeriod :=
    isClosed_Icc.mem_of_tendsto (hlabel0 0)
      (Eventually.of_forall fun j => (A (t j)).label0_normalized)
  have hnorm1 : sigma1 0 ∈ Icc (0 : ℝ) curvePeriod :=
    isClosed_Icc.mem_of_tendsto (hlabel1 0)
      (Eventually.of_forall fun j => (A (t j)).label1_normalized)
  have hcircle : angularPoint (frequency * delta) = angularPoint 0 := by
    have hh := (contDiff_angularPoint.continuous.tendsto (frequency * delta)).comp
      (tendsto_const_nhds.mul hdelta)
    have hh' : Tendsto (fun _ : ℕ => angularPoint 0) atTop
        (𝓝 (angularPoint (frequency * delta))) := by
      simpa only [Function.comp_def, (A _).offset_circle] using hh
    exact tendsto_nhds_unique hh' tendsto_const_nhds
  obtain ⟨s2, Q, hs2, hQvalue, hQcol, hQmap⟩ :=
    M64.observedWeakAnnulus_varying_trace_subsequence e he hei hread
      (fun j => hc0.comp ((A (t j)).labels_continuous hH0 hH1).1)
      (fun j => hc1.comp ((A (t j)).labels_continuous hH0 hH1).2)
      (Eventually.of_forall fun x => (hc0.tendsto (sigma0 x)).comp (hlabel0 x))
      (Eventually.of_forall fun x => (hc1.tendsto (sigma1 x)).comp (hlabel1 x))
      (fun j => (A (t j)).annulus) (fun j i => hC (t j) i)
  let s := t ∘ s2
  have hUfinal : WeakConverges (fun j => (A (s j)).phase) U :=
    fun L => ((hU L).comp hs1.tendsto_atTop).comp hs2.tendsto_atTop
  have hWfinal (i : Fin 2) : WeakConverges (fun j => (A (s j)).phaseColumn i) (W i) :=
    fun L => ((hW i L).comp hs1.tendsto_atTop).comp hs2.tendsto_atTop
  have hafinal : ∀ᵐ p ∂mu, Tendsto (fun j => (A (s j)).phase p) atTop (𝓝 (U p)) := by
    filter_upwards [ha] with p hp
    exact (hp.comp hs1.tendsto_atTop).comp hs2.tendsto_atTop
  have hobs : (fun p => R (e (Q.map p))) =ᵐ[mu] fun p => angularPoint (frequency * U p) := by
    have hall : ∀ᵐ p ∂mu, ∀ j, R (e ((A (s j)).annulus.map p)) =
        angularPoint (frequency * (A (s j)).phase p) :=
      ae_all_iff.mpr fun j => (A (s j)).phase_observation
    filter_upwards [hQmap, hafinal, hall] with p hpQ hpU hpall
    have hleft := ((R.continuous.comp he.continuous).tendsto (Q.map p)).comp hpQ
    have hright := (contDiff_angularPoint.continuous.tendsto (frequency * U p)).comp
      (tendsto_const_nhds.mul hpU)
    have hright' : Tendsto (fun j => R (e ((A (s j)).annulus.map p))) atTop
        (𝓝 (angularPoint (frequency * U p))) := by
      simpa only [Function.comp_def, hpall] using hright
    exact tendsto_nhds_unique hleft hright'
  let L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D := {
    label0 := sigma0
    label1 := sigma1
    label0_monotone := hmono0
    label1_monotone := hmono1
    label0_period := hperiod0
    label1_period := hperiod1
    label0_normalized := hnorm0
    label1_normalized := hnorm1
    annulus := Q
    phase := U
    phaseColumn := W
    phase_weak := hw
    phase_observation := hobs
    offset := delta
    offset_circle := hcircle
    phase_boundary := fun phi hphi => by
      simpa only [htrace0, htrace1] using hgreen phi hphi
    phase_seam := hseam }
  exact ⟨s, L, (hs0.comp hs1).comp hs2, hQvalue, hQcol, hQmap, hUfinal, hWfinal, hafinal,
    (fun x => (hlabel0 x).comp hs2.tendsto_atTop),
    (fun x => (hlabel1 x).comp hs2.tendsto_atTop), hdelta.comp hs2.tendsto_atTop⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus
