import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.TietzeExtension
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Arcs
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Counting
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Brouwer

namespace Poincare.Topology.Plane.Jordan

open Metric Set Function Bornology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def BrouwerFPT : Prop :=
  ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x

theorem crossing (hbr : BrouwerFPT) {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d)
    (h v : ℝ → Plane)
    (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
    (hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc a b ∧ h t 1 ∈ Icc c d)
    (hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc a b ∧ v t 1 ∈ Icc c d)
    (hh1 : h (-1) 0 = a) (hh2 : h 1 0 = b)
    (hv1 : v (-1) 1 = c) (hv2 : v 1 1 = d) :
    ∃ s ∈ Icc (-1:ℝ) 1, ∃ t ∈ Icc (-1:ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon

  set Q : Set Plane := {p | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-1:ℝ) 1} with hQdef
  have hQ0 : ∀ p ∈ Q, p 0 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.1
  have hQ1 : ∀ p ∈ Q, p 1 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.2

  have hconv : Convex ℝ Q := by
    have c0 : Convex ℝ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
    have c1 : Convex ℝ {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
    exact c0.inter c1

  have hcomp : IsCompact Q := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have d0 : IsClosed {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (0:Fin 2)).continuous
      have d1 : IsClosed {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (1:Fin 2)).continuous
      exact d0.inter d1
    · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 2)).subset
      intro p hp
      simp only [mem_closedBall, dist_zero_right]
      have h0 : |p 0| ≤ 1 := abs_le.2 ⟨hp.1.1, hp.1.2⟩
      have h1 : |p 1| ≤ 1 := abs_le.2 ⟨hp.2.1, hp.2.2⟩
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by ring, Real.sqrt_sq]; norm_num]
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  have hne0 : Q.Nonempty := by
    refine ⟨0, ?_, ?_⟩ <;>
      · simp only [mem_Icc, show (0:Plane) 0 = 0 from rfl, show (0:Plane) 1 = 0 from rfl]
        norm_num

  let N : Plane → ℝ := fun p => max |h (p 0) 0 - v (p 1) 0| |h (p 0) 1 - v (p 1) 1|
  let n0 : Plane → ℝ := fun p => (v (p 1) 0 - h (p 0) 0) / N p
  let n1 : Plane → ℝ := fun p => (h (p 0) 1 - v (p 1) 1) / N p
  let F : Plane → Plane := fun p => !₂[n0 p, n1 p]
  have hNnn : ∀ p, 0 ≤ N p := fun p => le_trans (abs_nonneg _) (le_max_left _ _)

  have hNpos : ∀ p ∈ Q, 0 < N p := by
    intro p hp
    rcases (hNnn p).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hNz : N p = 0 := heq.symm
      have hA0 : |h (p 0) 0 - v (p 1) 0| ≤ N p := le_max_left _ _
      have hB0 : |h (p 0) 1 - v (p 1) 1| ≤ N p := le_max_right _ _
      rw [hNz] at hA0 hB0
      have eA : h (p 0) 0 = v (p 1) 0 := by
        have := le_antisymm hA0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      have eB : h (p 0) 1 = v (p 1) 1 := by
        have := le_antisymm hB0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      refine hcon (p 0) (hQ0 p hp) (p 1) (hQ1 p hp) ?_
      ext i; fin_cases i
      · exact eA
      · exact eB

  have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have mt0 : MapsTo (fun p : Plane => p 0) Q (Icc (-1:ℝ) 1) := fun p hp => hQ0 p hp
  have mt1 : MapsTo (fun p : Plane => p 1) Q (Icc (-1:ℝ) 1) := fun p hp => hQ1 p hp
  have hHx0 : ContinuousOn (fun p : Plane => h (p 0) 0) Q :=
    (hc0.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hHx1 : ContinuousOn (fun p : Plane => h (p 0) 1) Q :=
    (hc1.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hVx0 : ContinuousOn (fun p : Plane => v (p 1) 0) Q :=
    (hc0.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hVx1 : ContinuousOn (fun p : Plane => v (p 1) 1) Q :=
    (hc1.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hNcont : ContinuousOn N Q :=
    ContinuousOn.sup ((hHx0.sub hVx0).abs) ((hHx1.sub hVx1).abs)
  have hn0c : ContinuousOn n0 Q :=
    (hVx0.sub hHx0).div hNcont (fun p hp => (hNpos p hp).ne')
  have hn1c : ContinuousOn n1 Q :=
    (hHx1.sub hVx1).div hNcont (fun p hp => (hNpos p hp).ne')
  have hFcont : ContinuousOn F Q := by
    have hG : ContinuousOn (fun p : Plane => (![n0 p, n1 p] : Fin 2 → ℝ)) Q := by
      rw [continuousOn_pi]
      intro i; fin_cases i
      · simpa using hn0c
      · simpa using hn1c
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn hG

  have hbound : ∀ p ∈ Q, |n0 p| ≤ 1 ∧ |n1 p| ≤ 1 := by
    intro p hp
    have hN := hNpos p hp
    refine ⟨?_, ?_⟩
    · show |(v (p 1) 0 - h (p 0) 0) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      calc |v (p 1) 0 - h (p 0) 0| = |h (p 0) 0 - v (p 1) 0| := abs_sub_comm _ _
        _ ≤ N p := le_max_left _ _
    · show |(h (p 0) 1 - v (p 1) 1) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      exact le_max_right _ _
  have hmaps : MapsTo F Q Q := by
    intro p hp
    obtain ⟨hb0, hb1⟩ := hbound p hp
    exact ⟨mem_Icc.2 (abs_le.1 hb0), mem_Icc.2 (abs_le.1 hb1)⟩

  let f : C(Q, Q) := ⟨fun p => ⟨F p.1, hmaps p.2⟩, by
    apply Continuous.subtype_mk; exact hFcont.restrict⟩
  obtain ⟨x, hx⟩ := hbr Q hconv hcomp hne0 f
  set p₀ : Plane := (x : Plane) with hp0def
  have hp0Q : p₀ ∈ Q := x.2
  have hN := hNpos p₀ hp0Q
  have hfix : F p₀ = p₀ := congrArg Subtype.val hx
  have hfix0 : p₀ 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := by
    have e : (F p₀) 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := rfl
    rw [← e, hfix]
  have hfix1 : p₀ 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := by
    have e : (F p₀) 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := rfl
    rw [← e, hfix]

  have a0 : |p₀ 0| = |h (p₀ 0) 0 - v (p₀ 1) 0| / N p₀ := by
    conv_lhs => rw [hfix0]
    rw [abs_div, abs_of_pos hN, abs_sub_comm]
  have a1 : |p₀ 1| = |h (p₀ 0) 1 - v (p₀ 1) 1| / N p₀ := by
    conv_lhs => rw [hfix1]
    rw [abs_div, abs_of_pos hN]
  have hbdry : |p₀ 0| = 1 ∨ |p₀ 1| = 1 := by
    rcases le_total |h (p₀ 0) 1 - v (p₀ 1) 1| |h (p₀ 0) 0 - v (p₀ 1) 0| with hle | hle
    · left
      have hNA : N p₀ = |h (p₀ 0) 0 - v (p₀ 1) 0| := max_eq_left hle
      rw [a0, hNA]; exact div_self (by rw [← hNA]; exact hN.ne')
    · right
      have hNB : N p₀ = |h (p₀ 0) 1 - v (p₀ 1) 1| := max_eq_right hle
      rw [a1, hNB]; exact div_self (by rw [← hNB]; exact hN.ne')

  rcases hbdry with hb | hb
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    ·
      have hh0b : h (p₀ 0) 0 = b := by rw [hpos]; exact hh2
      have hvle : v (p₀ 1) 0 ≤ b := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.2
      have : p₀ 0 ≤ 0 := by
        rw [hfix0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    ·
      have hh0a : h (p₀ 0) 0 = a := by rw [hneg]; exact hh1
      have hvge : a ≤ v (p₀ 1) 0 := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.1
      have : 0 ≤ p₀ 0 := by rw [hfix0]; exact div_nonneg (by linarith) hN.le
      linarith
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    ·
      have hv1d : v (p₀ 1) 1 = d := by rw [hpos]; exact hv2
      have hhle : h (p₀ 0) 1 ≤ d := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.2
      have : p₀ 1 ≤ 0 := by
        rw [hfix1]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    ·
      have hv1c : v (p₀ 1) 1 = c := by rw [hneg]; exact hv1
      have hhge : c ≤ h (p₀ 0) 1 := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.1
      have : 0 ≤ p₀ 1 := by rw [hfix1]; exact div_nonneg (by linarith) hN.le
      linarith

theorem one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  have h : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  rw [h]; norm_num

theorem isConnected_compl_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {x : Plane | R < ‖x‖} := by
  have hconn : IsConnected ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) :=
    (isConnected_sphere one_lt_rank_plane 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have hset : {x : Plane | R < ‖x‖}
      = (fun p : Plane × ℝ => p.2 • p.1) '' ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) := by
    ext x
    simp only [mem_setOf_eq, mem_image, mem_prod, mem_Ioi, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR ht)]
      exact ht
  rw [hset]; exact himg

section JordanCurveData

variable (r : sphere (0 : Plane) 1 → Plane)

theorem jordanCurve_isCompact (hcont : Continuous r) : IsCompact (range r) :=
  isCompact_range hcont

theorem jordanCurve_isClosed (hcont : Continuous r) : IsClosed (range r) :=
  (jordanCurve_isCompact r hcont).isClosed

theorem isOpen_compl_jordanCurve (hcont : Continuous r) : IsOpen (range r)ᶜ :=
  (jordanCurve_isClosed r hcont).isOpen_compl

theorem r_isClosedEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

theorem r_isEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsEmbedding r :=
  (r_isClosedEmbedding r hcont hinj).isEmbedding

noncomputable def jordanCurveHomeo (hcont : Continuous r) (hinj : Injective r) :
    sphere (0 : Plane) 1 ≃ₜ (range r) :=
  (r_isEmbedding r hcont hinj).toHomeomorph

private theorem exists_jordanCurve_bound (hcont : Continuous r) :
    ∃ R : ℝ, 0 ≤ R ∧ range r ⊆ closedBall (0 : Plane) R := by
  obtain ⟨R, hR⟩ := (jordanCurve_isCompact r hcont).isBounded.subset_closedBall 0
  exact ⟨max R 0, le_max_right R 0,
    hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩

theorem exists_unbounded_component (hcont : Continuous r) :
    ∃ x ∈ (range r)ᶜ, ¬ IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  have hEconn : IsConnected {z : Plane | R < ‖z‖} := isConnected_compl_closedBall hR0
  have hEsub : {z : Plane | R < ‖z‖} ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  have hEnb : ¬ IsBounded {z : Plane | R < ‖z‖} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    obtain ⟨z, hz⟩ := NormedSpace.exists_lt_norm ℝ Plane (max M R)
    have hzE : z ∈ {z : Plane | R < ‖z‖} := lt_of_le_of_lt (le_max_right M R) hz
    have hzM := hM hzE
    rw [mem_closedBall_zero_iff] at hzM
    exact absurd (le_max_left M R) (not_le.2 (lt_of_lt_of_le hz hzM))
  obtain ⟨x, hxE⟩ := hEconn.nonempty
  refine ⟨x, hEsub hxE, ?_⟩
  have hEcomp : {z : Plane | R < ‖z‖} ⊆ connectedComponentIn (range r)ᶜ x :=
    hEconn.isPreconnected.subset_connectedComponentIn hxE hEsub
  exact fun hbdd => hEnb (hbdd.subset hEcomp)

theorem unbounded_component_unique (hcont : Continuous r) {x y : Plane}
    (hxu : ¬ IsBounded (connectedComponentIn (range r)ᶜ x))
    (hyu : ¬ IsBounded (connectedComponentIn (range r)ᶜ y)) :
    connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  set E : Set Plane := {z : Plane | R < ‖z‖} with hE
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)

  have meetsE : ∀ z : Plane,
      ¬ IsBounded (connectedComponentIn (range r)ᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn (range r)ᶜ z := by
    intro z hz
    by_contra hcon
    push Not at hcon
    apply hz
    have hsubBall : connectedComponentIn (range r)ᶜ z ⊆ closedBall (0 : Plane) R := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hEcomp : E ⊆ connectedComponentIn (range r)ᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub

  obtain ⟨wx, hwxE, hwxc⟩ := meetsE x hxu
  obtain ⟨wy, hwyE, hwyc⟩ := meetsE y hyu
  have hx : connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwxc, ← connectedComponentIn_eq (hEcomp hwxE)]
  have hy : connectedComponentIn (range r)ᶜ y = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwyc, ← connectedComponentIn_eq (hEcomp hwyE)]
  rw [hx, hy]

theorem isOpen_component (hcont : Continuous r) (x : Plane) :
    IsOpen (connectedComponentIn (range r)ᶜ x) :=
  (isOpen_compl_jordanCurve r hcont).connectedComponentIn

theorem isPathConnected_component (hcont : Continuous r) {x : Plane}
    (hx : x ∈ (range r)ᶜ) :
    IsPathConnected (connectedComponentIn (range r)ᶜ x) :=
  ((isOpen_component r hcont x).isConnected_iff_isPathConnected).mp
    (isConnected_connectedComponentIn_iff.mpr hx)

end JordanCurveData

theorem arc_not_separates (hbr : BrouwerFPT) {A : Set Plane}
    (φ : A ≃ₜ unitInterval) : IsConnected Aᶜ := by
  classical

  haveI : CompactSpace ↥unitInterval := inferInstance
  haveI hcsA : CompactSpace ↥A := φ.symm.compactSpace
  have hAcpt : IsCompact A := isCompact_iff_compactSpace.mpr hcsA
  have hAcl : IsClosed A := hAcpt.isClosed
  have hAbd : IsBounded A := hAcpt.isBounded
  have hAopen : IsOpen Aᶜ := hAcl.isOpen_compl

  haveI : TietzeExtension ↥A := TietzeExtension.of_homeo φ
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hAcl (ContinuousMap.id ↥A)
  set ρ : Plane → Plane := fun x => (g x : Plane) with hρdef
  have hρcont : Continuous ρ := continuous_subtype_val.comp g.continuous
  have hρmem : ∀ x, ρ x ∈ A := fun x => (g x).2
  have hρid : ∀ a ∈ A, ρ a = a := by
    intro a ha
    have h1 := DFunLike.congr_fun hg ⟨a, ha⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.id_apply] at h1
    show (g a : Plane) = a
    exact congrArg Subtype.val h1

  obtain ⟨R0, hR0, hAsub⟩ : ∃ R0 : ℝ, 0 ≤ R0 ∧ A ⊆ closedBall (0 : Plane) R0 := by
    obtain ⟨R, hR⟩ := hAbd.subset_closedBall (0 : Plane)
    exact ⟨max R 0, le_max_right R 0,
      hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩
  set E : Set Plane := {z : Plane | R0 < ‖z‖} with hEdef
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ Aᶜ := by
    intro z hz hzA
    have := hAsub hzA
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hpAc : p ∈ Aᶜ := hEsub hpE
  have hEcomp : E ⊆ connectedComponentIn Aᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub

  have meetsE : ∀ z, z ∈ Aᶜ → ¬ IsBounded (connectedComponentIn Aᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn Aᶜ z := by
    intro z _ hzu
    by_contra hcon
    push Not at hcon
    apply hzu
    have hsubBall : connectedComponentIn Aᶜ z ⊆ closedBall (0 : Plane) R0 := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  refine ⟨⟨p, hpAc⟩, ?_⟩

  by_cases hbdd : ∃ o ∈ Aᶜ, IsBounded (connectedComponentIn Aᶜ o)
  ·
    exfalso
    obtain ⟨o, hoAc, hKbd⟩ := hbdd
    set K : Set Plane := connectedComponentIn Aᶜ o with hKdef
    have hoK : o ∈ K := mem_connectedComponentIn hoAc
    have hKopen : IsOpen K := hAopen.connectedComponentIn
    have hoA : o ∉ A := hoAc

    have hfrontier : frontier K ⊆ A := by
      intro x hx
      by_contra hxA
      have hxAc : x ∈ Aᶜ := hxA
      have hxcl : x ∈ closure K := frontier_subset_closure hx
      have hxnK : x ∉ K := by
        intro hxK
        have : x ∈ K ∩ frontier K := ⟨hxK, hx⟩
        rw [hKopen.inter_frontier_eq] at this
        exact absurd this (Set.notMem_empty x)
      have hCxopen : IsOpen (connectedComponentIn Aᶜ x) := hAopen.connectedComponentIn
      have hxCx : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hxAc
      rw [_root_.mem_closure_iff] at hxcl
      obtain ⟨w, hwCx, hwK⟩ := hxcl _ hCxopen hxCx
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwCx
      rw [hKdef] at hwK
      have e2 : connectedComponentIn Aᶜ o = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwK
      rw [e1, ← e2] at hxCx
      rw [← hKdef] at hxCx
      exact hxnK hxCx

    obtain ⟨R, hRpos, hAR, hKR⟩ :
        ∃ R : ℝ, 0 < R ∧ A ⊆ ball o R ∧ K ⊆ ball o R := by
      obtain ⟨rA, hrA⟩ := hAbd.subset_closedBall o
      obtain ⟨rK, hrK⟩ := hKbd.subset_closedBall o
      refine ⟨max (max rA rK) 0 + 1, by positivity, ?_, ?_⟩
      · exact hrA.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_left rA rK).trans (le_max_left _ 0)) (lt_add_one _)))
      · exact hrK.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_right rA rK).trans (le_max_left _ 0)) (lt_add_one _)))

    set Q : Plane → Plane := K.piecewise ρ id with hQdef
    have hQcont : Continuous Q := by
      refine Continuous.piecewise ?_ hρcont continuous_id
      intro a ha
      show ρ a = id a
      simpa using hρid a (hfrontier ha)
    have hQA : ∀ z ∈ K, Q z = ρ z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_mem _ _ _ hz
    have hQid : ∀ z, z ∉ K → Q z = z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_notMem _ _ _ hz
    have hQne : ∀ z, Q z ≠ o := by
      intro z
      by_cases hz : z ∈ K
      · rw [hQA z hz]; intro h; exact hoA (h ▸ hρmem z)
      · rw [hQid z hz]; intro h; apply hz; rw [h]; exact hoK

    set Φ : Plane → Plane := fun z => o - R • (‖Q z - o‖⁻¹ • (Q z - o)) with hΦdef
    have hΦcont : Continuous Φ := by
      have h1 : Continuous (fun z => Q z - o) := hQcont.sub continuous_const
      have h2 : Continuous (fun z => (‖Q z - o‖)⁻¹) :=
        h1.norm.inv₀ (fun z => by
          simp only [ne_eq, norm_eq_zero, sub_eq_zero]; exact hQne z)
      have hRcont : Continuous (fun _ : Plane => R) := continuous_const
      exact continuous_const.sub (hRcont.smul (h2.smul h1))
    have hΦsphere : ∀ z, ‖Φ z - o‖ = R := by
      intro z
      have hne : Q z - o ≠ 0 := sub_ne_zero.mpr (hQne z)
      have hw1 : ‖‖Q z - o‖⁻¹ • (Q z - o)‖ = 1 := norm_smul_inv_norm hne
      have he : Φ z - o = -(R • (‖Q z - o‖⁻¹ • (Q z - o))) := by
        simp only [hΦdef]; abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hRpos.le, hw1,
        mul_one]

    set D : Set Plane := closedBall o R with hDdef
    have hΦD : ∀ z ∈ D, Φ z ∈ D := by
      intro z _
      rw [hDdef, mem_closedBall]
      exact le_of_eq (by rw [dist_eq_norm]; exact hΦsphere z)
    have hDconv : Convex ℝ D := convex_closedBall o R
    have hDcomp : IsCompact D := isCompact_closedBall o R
    have hDne : D.Nonempty := ⟨o, by rw [hDdef]; exact mem_closedBall_self hRpos.le⟩

    let F : C(↥D, ↥D) :=
      ⟨fun z => ⟨Φ z.1, hΦD z.1 z.2⟩,
        Continuous.subtype_mk (hΦcont.comp continuous_subtype_val) _⟩
    obtain ⟨x, hx⟩ := hbr D hDconv hDcomp hDne F
    set x0 : Plane := (x : Plane) with hx0
    have hfix : Φ x0 = x0 := congrArg Subtype.val hx
    have hx0R : ‖x0 - o‖ = R := by rw [← hfix]; exact hΦsphere x0
    have hx0nK : x0 ∉ K := by
      intro hk
      have hin := hKR hk
      rw [mem_ball, dist_eq_norm, hx0R] at hin
      exact lt_irrefl R hin
    have hQx0 : Q x0 = x0 := hQid x0 hx0nK
    have hcompute : Φ x0 = o - (x0 - o) := by
      simp only [hΦdef]
      rw [hQx0, hx0R, smul_smul, mul_inv_cancel₀ hRpos.ne', one_smul]
    rw [hcompute] at hfix
    have hz : x0 - o = 0 := by
      have e : (2 : ℝ) • (x0 - o) = x0 - (o - (x0 - o)) := by rw [two_smul]; abel
      have h20 : (2 : ℝ) • (x0 - o) = 0 := by rw [e, hfix]; abel
      exact (smul_eq_zero.mp h20).resolve_left (by norm_num)
    rw [hz, norm_zero] at hx0R
    exact absurd hx0R.symm hRpos.ne'
  ·
    push Not at hbdd
    have hAeq : Aᶜ ⊆ connectedComponentIn Aᶜ p := by
      intro x hx
      obtain ⟨w, hwE, hwx⟩ := meetsE x hx (hbdd x hx)
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwx
      have e2 : connectedComponentIn Aᶜ p = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq (hEcomp hwE)
      have hxc : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hx
      rw [e1, ← e2] at hxc
      exact hxc
    have hsup : connectedComponentIn Aᶜ p ⊆ Aᶜ := connectedComponentIn_subset Aᶜ p
    rw [Set.Subset.antisymm hAeq hsup]
    exact (isConnected_connectedComponentIn_iff.mpr hpAc).isPreconnected

theorem component_boundary_eq (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    {x : Plane} (hx : x ∈ (range r)ᶜ)
    (_hy : ∃ y ∈ (range r)ᶜ,
      connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ x) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r := by
  classical
  set U := connectedComponentIn (range r)ᶜ x with hUdef
  have hUopen : IsOpen U := isOpen_component r hcont x
  have hxU : x ∈ U := mem_connectedComponentIn hx

  have hsub : frontier U ⊆ range r := by
    intro w hw
    by_contra hwr
    have hwc : w ∈ (range r)ᶜ := hwr
    have hwcl : w ∈ closure U := frontier_subset_closure hw
    have hWopen : IsOpen (connectedComponentIn (range r)ᶜ w) :=
      isOpen_component r hcont w
    have hwW : w ∈ connectedComponentIn (range r)ᶜ w := mem_connectedComponentIn hwc
    rw [_root_.mem_closure_iff] at hwcl
    obtain ⟨v, hvW, hvU⟩ := hwcl _ hWopen hwW
    have e1 : connectedComponentIn (range r)ᶜ w = connectedComponentIn (range r)ᶜ v :=
      connectedComponentIn_eq hvW
    have e2 : U = connectedComponentIn (range r)ᶜ v := connectedComponentIn_eq hvU
    have hwU : w ∈ U := by rw [e2, ← e1]; exact hwW
    have : w ∈ U ∩ frontier U := ⟨hwU, hw⟩
    rw [hUopen.inter_frontier_eq] at this
    exact absurd this (Set.notMem_empty w)

  by_contra hne
  have hssub : frontier U ⊂ range r := hsub.ssubset_of_ne hne

  set C : Set (sphere (0 : Plane) 1) := r ⁻¹' frontier U with hCdef
  have hCclosed : IsClosed C := isClosed_frontier.preimage hcont
  have hCne : C ≠ univ := by
    intro h
    apply hne
    refine Set.Subset.antisymm hsub ?_
    intro w hw
    obtain ⟨s, rfl⟩ := hw
    have hsC : s ∈ C := h.symm ▸ mem_univ s
    exact hsC
  obtain ⟨A₀, hCA0, hA0ne, hA0closed, ⟨e0⟩⟩ :=
    Poincare.Topology.Plane.Jordan.Arcs.exists_proper_arc hCclosed hCne
  set A : Set Plane := r '' A₀ with hAdef

  haveI hcsSphere : CompactSpace (sphere (0 : Plane) 1) :=
    Poincare.Topology.Plane.Jordan.Arcs.circleHomeoSphere.compactSpace
  haveI hcsA0 : CompactSpace ↥A₀ := isCompact_iff_compactSpace.mp hA0closed.isCompact
  have eImg : (↥A₀) ≃ₜ (↥A) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.image r A₀ hinj)
      (continuous_induced_rng.2 (hcont.comp continuous_subtype_val))
  have eA : A ≃ₜ unitInterval := eImg.symm.trans e0

  have hAr : A ⊆ range r := by
    rw [hAdef]; rintro _ ⟨s, _, rfl⟩; exact ⟨s, rfl⟩
  have hfrA : frontier U ⊆ A := by
    rw [hAdef]
    intro w hw
    obtain ⟨s, rfl⟩ := hsub hw
    exact ⟨s, hCA0 hw, rfl⟩
  obtain ⟨s₀, hs₀⟩ := (Set.ne_univ_iff_exists_notMem A₀).1 hA0ne
  have hq'r : r s₀ ∈ range r := ⟨s₀, rfl⟩
  have hq'A : r s₀ ∉ A := by
    rw [hAdef]
    rintro ⟨s, hsA, hss⟩
    exact hs₀ (hinj hss ▸ hsA)

  have hAconn : IsConnected Aᶜ := arc_not_separates hbr eA

  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset (range r)ᶜ x
  have hUAc : U ⊆ Aᶜ := hUsub.trans (compl_subset_compl.mpr hAr)
  have hxAc : x ∈ Aᶜ := hUAc hxU
  have hVopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hcover : Aᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro w hwAc
    by_cases hwcl : w ∈ closure U
    · left
      by_contra hwU
      have hfr : w ∈ frontier U := by
        refine ⟨hwcl, ?_⟩
        rw [hUopen.interior_eq]; exact hwU
      exact hwAc (hfrA hfr)
    · right; exact hwcl
  have hqV : r s₀ ∈ (closure U)ᶜ := by
    intro hcl
    have hnU : r s₀ ∉ U := fun h => (hUsub h) hq'r
    have hfr : r s₀ ∈ frontier U := by
      refine ⟨hcl, ?_⟩
      rw [hUopen.interior_eq]; exact hnU
    exact hq'A (hfrA hfr)
  obtain ⟨w, _, hwU, hwV⟩ :=
    hAconn.isPreconnected U (closure U)ᶜ hUopen hVopen hcover
      ⟨x, hxAc, hxU⟩ ⟨r s₀, hq'A, hqV⟩
  exact hwV (subset_closure hwU)

private lemma complexLIE_one : Arcs.complexLIE (1 : ℂ) = !₂[(1:ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.one_re, Complex.one_im, one_smul, zero_smul, add_zero,
    EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

private lemma complexLIE_negOne : Arcs.complexLIE (-1 : ℂ) = !₂[(-1:ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (-1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
    zero_smul, add_zero, EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

theorem exists_farthest_pair {r : sphere (0 : Plane) 1 → Plane}
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ a ∈ range r, ∃ b ∈ range r,
      (∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ dist a b) ∧ a ≠ b := by
  have hcpt : IsCompact (range r) := jordanCurve_isCompact r hcont

  have hs1 : (!₂[(1:ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  have hs2 : (!₂[(-1:ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  set s1 : sphere (0 : Plane) 1 := ⟨!₂[(1:ℝ), 0], hs1⟩ with hs1def
  set s2 : sphere (0 : Plane) 1 := ⟨!₂[(-1:ℝ), 0], hs2⟩ with hs2def
  have hs12 : s1 ≠ s2 := by
    intro h
    rw [hs1def, hs2def, Subtype.mk_eq_mk] at h
    have hh : (!₂[(1:ℝ), 0] : Plane) 0 = (!₂[(-1:ℝ), 0] : Plane) 0 := by rw [h]
    norm_num [PiLp.toLp_apply] at hh
  have hne : (range r).Nonempty := ⟨r s1, mem_range_self _⟩
  have hprod : IsCompact ((range r) ×ˢ (range r)) := hcpt.prod hcpt
  have hpne : ((range r) ×ˢ (range r)).Nonempty := hne.prod hne
  obtain ⟨⟨a, b⟩, hmem, hmax⟩ :=
    hprod.exists_isMaxOn hpne
      (continuous_dist.continuousOn (s := (range r) ×ˢ (range r)))
  rw [mem_prod] at hmem
  refine ⟨a, hmem.1, b, hmem.2, ?_, ?_⟩
  · intro z hz w hw
    exact isMaxOn_iff.mp hmax (z, w) (mem_prod.mpr ⟨hz, hw⟩)
  · intro hEq
    have hd0 : dist a b = 0 := by rw [hEq, dist_self]
    have hle : dist (r s1) (r s2) ≤ dist a b :=
      isMaxOn_iff.mp hmax (r s1, r s2) (mem_prod.mpr ⟨mem_range_self _, mem_range_self _⟩)
    rw [hd0] at hle
    exact hs12 (hinj (eq_of_dist_eq_zero (le_antisymm hle dist_nonneg)))

theorem exists_similarity {a b : Plane} (hab : a ≠ b) :
    ∃ T : Plane ≃ₜ Plane,
      (∀ z w, dist (T z) (T w) = (2 / dist a b) * dist z w) ∧
        T a = !₂[(-1:ℝ), 0] ∧ T b = !₂[(1:ℝ), 0] := by
  set L := Arcs.complexLIE with hL
  set A : ℂ := L.symm a with hA
  set B : ℂ := L.symm b with hB
  have hBAne : B ≠ A := by
    intro h; exact hab (L.symm.injective h).symm
  have hABne : B - A ≠ 0 := sub_ne_zero.mpr hBAne
  set α : ℂ := 2 / (B - A) with hα
  have hαne : α ≠ 0 := by rw [hα]; exact div_ne_zero two_ne_zero hABne
  set β : ℂ := -(A + B) / (B - A) with hβ
  set e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ α hαne).trans (Homeomorph.addRight β) with he
  have he_apply : ∀ w : ℂ, e w = α * w + β := by
    intro w
    rw [he]
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
  set T : Plane ≃ₜ Plane := (L.symm.toHomeomorph).trans (e.trans L.toHomeomorph) with hT
  have hT_apply : ∀ w : Plane, T w = L (α * L.symm w + β) := by
    intro w
    rw [hT]
    simp only [Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, he_apply]
  refine ⟨T, ?_, ?_, ?_⟩
  ·
    intro z w
    rw [hT_apply, hT_apply, L.dist_map, dist_eq_norm,
      show (α * L.symm z + β) - (α * L.symm w + β) = α * (L.symm z - L.symm w) by ring,
      norm_mul, ← dist_eq_norm, L.symm.dist_map]
    have hαnorm : ‖α‖ = 2 / dist a b := by
      rw [hα, norm_div]
      rw [show ‖(2:ℂ)‖ = 2 by norm_num]
      congr 1
      rw [hB, hA, ← dist_eq_norm, L.symm.dist_map, dist_comm]
    rw [hαnorm]
  ·
    have hval : α * A + β = -1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hA, hval, hL]; exact complexLIE_negOne
  ·
    have hval : α * B + β = 1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hB, hval, hL]; exact complexLIE_one

theorem isBounded_image_scaling {T : Plane → Plane} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ z w, dist (T z) (T w) = c * dist z w) (K : Set Plane) :
    IsBounded (T '' K) ↔ IsBounded K := by
  simp only [Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun x hx y hy => ?_⟩
    have h := hC (mem_image_of_mem T hx) (mem_image_of_mem T hy)
    rw [hscale] at h
    rw [le_div_iff₀ hc, mul_comm]; exact h
  · rintro ⟨C, hC⟩
    refine ⟨c * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hC hx hy) hc.le

private lemma dist_sq_coord (z w : Plane) :
    dist z w ^ 2 = (z 0 - w 0) ^ 2 + (z 1 - w 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem normalized_subset_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    range r ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} := by
  intro z hz
  have hza : dist z (!₂[(-1:ℝ), 0]) ≤ 2 := hfar z hz _ hm
  have hzb : dist z (!₂[(1:ℝ), 0]) ≤ 2 := hfar z hz _ hp
  have hza2 : dist z (!₂[(-1:ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(-1:ℝ), 0] : Plane))]
  have hzb2 : dist z (!₂[(1:ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(1:ℝ), 0] : Plane))]
  rw [dist_sq_coord] at hza2 hzb2
  have ea0 : (!₂[(-1:ℝ), 0] : Plane) 0 = -1 := by simp
  have ea1 : (!₂[(-1:ℝ), 0] : Plane) 1 = 0 := by simp
  have eb0 : (!₂[(1:ℝ), 0] : Plane) 0 = 1 := by simp
  have eb1 : (!₂[(1:ℝ), 0] : Plane) 1 = 0 := by simp
  rw [ea0, ea1] at hza2
  rw [eb0, eb1] at hzb2
  simp only [mem_setOf_eq, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]

theorem arc_path {S : Set Plane} {a b : Plane} (hj : JoinedIn S a b) :
    ∃ h : ℝ → Plane, ContinuousOn h (Icc (-1:ℝ) 1) ∧ h (-1) = a ∧ h 1 = b ∧
      ∀ t ∈ Icc (-1:ℝ) 1, h t ∈ S := by
  refine ⟨fun t => hj.somePath (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)),
    ?_, ?_, ?_, ?_⟩
  · exact (hj.somePath.continuous.comp
      (continuous_projIcc.comp (by fun_prop))).continuousOn
  · show hj.somePath _ = a
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.source
  · show hj.somePath _ = b
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.target
  · intro t _; exact hj.somePath_mem _

theorem segment_meets_curve (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (_hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ p ∈ range r, p 0 = 0 ∧ p 1 ∈ Icc (-2:ℝ) 2 := by

  have hsp : IsPathConnected (sphere (0:Plane) 1) :=
    isPathConnected_sphere one_lt_rank_plane 0 (by norm_num)
  haveI : PathConnectedSpace ↥(sphere (0:Plane) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsp
  have h1 : IsPathConnected (univ : Set ↥(sphere (0:Plane) 1)) :=
    pathConnectedSpace_iff_univ.mp ‹_›
  have hpc : IsPathConnected (range r) := by
    have := h1.image hcont; rwa [image_univ] at this
  have hjoin : JoinedIn (range r) (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) :=
    hpc.joinedIn _ hm _ hp
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hjoin
  have hrect := normalized_subset_rectangle hm hp hfar

  set v : ℝ → Plane := fun t => !₂[(0:ℝ), 2 * t] with hvdef
  have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) := by
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hv0 : ∀ t : ℝ, v t 0 = 0 := by intro t; simp [hvdef]
  have hv1 : ∀ t : ℝ, v t 1 = 2 * t := by intro t; simp [hvdef]

  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hrect (hhmem t ht)
  have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rw [mem_Icc] at ht
    refine ⟨?_, ?_⟩
    · rw [hv0]; simp
    · rw [hv1, mem_Icc]; constructor <;> nlinarith [ht.1, ht.2]
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  have hv1e : v (-1) 1 = -2 := by rw [hv1]; norm_num
  have hv2e : v 1 1 = 2 := by rw [hv1]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1e hv2e
  refine ⟨h s, hhmem s hs, ?_, ?_⟩
  · rw [heq, hv0]
  · rw [heq]; exact (hvE t ht).2

theorem exists_ymax_on_axis (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ l ∈ range r, l 0 = 0 ∧ ∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1 := by
  set Jax : Set Plane := {p ∈ range r | p 0 = 0} with hJax
  have hsub : Jax ⊆ range r := fun p hp => hp.1
  have hJaxcl : IsClosed Jax :=
    (jordanCurve_isClosed r hcont).inter (isClosed_eq (by fun_prop) continuous_const)
  have hJaxcpt : IsCompact Jax :=
    (jordanCurve_isCompact r hcont).of_isClosed_subset hJaxcl hsub
  have hne : Jax.Nonempty := by
    obtain ⟨p, hpr, hp0, _⟩ := segment_meets_curve hbr hcont hinj hm hp hfar
    exact ⟨p, hpr, hp0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨l, hlJax, hlmax⟩ :=
    hJaxcpt.exists_isMaxOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  refine ⟨l, hlJax.1, hlJax.2, ?_⟩
  intro p hpr hp0
  exact hlmax (show p ∈ Jax from ⟨hpr, hp0⟩)

private lemma planar_arc_homeo {K : Set Plane} {A : Set ↥K}
    (e : A ≃ₜ unitInterval) : Nonempty (((↑) '' A : Set Plane) ≃ₜ unitInterval) := by
  haveI : CompactSpace ↥A := e.symm.compactSpace
  let k : ↥A → Plane := fun a => ((a : ↥K) : Plane)
  have hkc : Continuous k := continuous_subtype_val.comp continuous_subtype_val
  have hki : Injective k := Subtype.coe_injective.comp Subtype.coe_injective
  have hemb : Topology.IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  have hrange : Set.range k = ((↑) '' A : Set Plane) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨((Homeomorph.setCongr hrange).symm.trans hemb.toHomeomorph.symm).trans e⟩

theorem jordan_arcs (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ J_n J_s : Set Plane,
      IsClosed J_n ∧ IsClosed J_s ∧
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} ∧
      Nonempty (J_n ≃ₜ unitInterval) ∧ Nonempty (J_s ≃ₜ unitInterval) ∧
      IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      IsPathConnected (J_s \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      ∃ l ∈ range r, l 0 = 0 ∧ (∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1) ∧ l ∈ J_n := by
  obtain ⟨l, hlr, hl0, hlmax⟩ := exists_ymax_on_axis hbr hcont hinj hm hp hfar
  set J := jordanCurveHomeo r hcont hinj with hJdef
  have hab : (!₂[(-1:ℝ), 0] : Plane) ≠ !₂[(1:ℝ), 0] := by
    intro h
    have h0 : (!₂[(-1:ℝ), 0] : Plane) 0 = (!₂[(1:ℝ), 0] : Plane) 0 := by rw [h]
    rw [show (!₂[(-1:ℝ), 0] : Plane) 0 = -1 from by simp,
        show (!₂[(1:ℝ), 0] : Plane) 0 = 1 from by simp] at h0
    norm_num at h0
  set x : sphere (0 : Plane) 1 := J.symm ⟨_, hm⟩ with hxdef
  set y : sphere (0 : Plane) 1 := J.symm ⟨_, hp⟩ with hydef
  have hxy : x ≠ y := by
    intro h
    exact hab (Subtype.ext_iff.mp (J.symm.injective h))
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpcA1, hpcA2⟩ := Arcs.jordanCurve_split J hxy

  have hJx : J x = ⟨_, hm⟩ := J.apply_symm_apply _
  have hJy : J y = ⟨_, hp⟩ := J.apply_symm_apply _

  set B₁ : Set Plane := (↑) '' A₁ with hB1
  set B₂ : Set Plane := (↑) '' A₂ with hB2
  have hBu : B₁ ∪ B₂ = range r := by
    rw [hB1, hB2, ← Set.image_union, hu, Set.image_univ, Subtype.range_coe]
  have hBi : B₁ ∩ B₂ = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} := by
    rw [hB1, hB2, ← Set.image_inter Subtype.coe_injective, hi, hJx, hJy,
      Set.image_pair]
  have hn1 : Nonempty (B₁ ≃ₜ unitInterval) := planar_arc_homeo e1
  have hn2 : Nonempty (B₂ ≃ₜ unitInterval) := planar_arc_homeo e2
  have hcl1 : IsClosed B₁ :=
    (isCompact_iff_compactSpace.mpr hn1.some.symm.compactSpace).isClosed
  have hcl2 : IsClosed B₂ :=
    (isCompact_iff_compactSpace.mpr hn2.some.symm.compactSpace).isClosed

  have hpcB1 : IsPathConnected (B₁ \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) := by
    have h := hpcA1.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  have hpcB2 : IsPathConnected (B₂ \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) := by
    have h := hpcA2.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h

  have hlB : l ∈ B₁ ∪ B₂ := by rw [hBu]; exact hlr
  rcases hlB with hl | hl
  · exact ⟨B₁, B₂, hcl1, hcl2, hBu, hBi, hn1, hn2, hpcB1, hpcB2, l, hlr, hl0, hlmax, hl⟩
  · refine ⟨B₂, B₁, hcl2, hcl1, ?_, ?_, hn2, hn1, hpcB2, hpcB1, l, hlr, hl0, hlmax, hl⟩
    · rw [Set.union_comm]; exact hBu
    · rw [Set.inter_comm]; exact hBi

theorem arc_isPathConnected {J : Set Plane} (e : ↥J ≃ₜ unitInterval) :
    IsPathConnected J := by
  haveI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0:ℝ) 1).isPathConnected (Set.nonempty_Icc.mpr (by norm_num)))
  have h1 : IsPathConnected (univ : Set unitInterval) := isPathConnected_univ
  have h2 := h1.image
    (show Continuous (fun x : unitInterval => ((e.symm x : ↥J) : Plane)) from
      continuous_subtype_val.comp e.symm.continuous)
  rw [Set.image_univ] at h2
  have hrange : (Set.range fun x : unitInterval => ((e.symm x : ↥J) : Plane)) = J := by
    ext p
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact (e.symm x).2
    · intro hp; exact ⟨e ⟨p, hp⟩, by simp⟩
  rwa [hrange] at h2

theorem arc_joinedIn {J : Set Plane} (e : ↥J ≃ₜ unitInterval)
    {a b : Plane} (ha : a ∈ J) (hb : b ∈ J) : JoinedIn J a b :=
  (arc_isPathConnected e).joinedIn a ha b hb

theorem vertical_meets_arc (hbr : BrouwerFPT) {J : Set Plane}
    (hJsub : J ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2})
    (hJoin : JoinedIn J (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {v : ℝ → Plane} (hvcont : ContinuousOn v (Icc (-1:ℝ) 1))
    (hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2)
    (hv1 : v (-1) 1 = -2) (hv2 : v 1 1 = 2) :
    ∃ t ∈ Icc (-1:ℝ) 1, v t ∈ J := by
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hJoin
  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hJsub (hhmem t ht)
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1 hv2
  exact ⟨t, ht, heq ▸ hhmem s hs⟩

private noncomputable def pathOfPiece {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) : Path (f (-1)) (f 1) :=
  Path.mk ⟨fun s : unitInterval => f (2 * (s : ℝ) - 1), by
      refine hf.comp_continuous (by fun_prop) (fun s => ?_)
      have hs := s.2; rw [Set.mem_Icc] at hs ⊢
      constructor <;> [linarith [hs.1]; linarith [hs.2]]⟩
    (by norm_num [Set.Icc.coe_zero]) (by norm_num [Set.Icc.coe_one])

private lemma pathOfPiece_range {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨s, rfl⟩
    have hs := s.2; rw [Set.mem_Icc] at hs
    exact ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨⟨(y + 1) / 2, by rw [Set.mem_Icc]; constructor <;> linarith⟩, ?_⟩
    show f (2 * ((y + 1) / 2) - 1) = f y
    congr 1; ring

theorem concatPath2 {f g : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hchain : f 1 = g (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = g 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1, c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 := by
  set P : Path (f (-1)) (g 1) :=
    (pathOfPiece hf).trans ((pathOfPiece hg).cast hchain rfl) with hP
  refine ⟨fun t => P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)), ?_, ?_, ?_, ?_⟩
  · exact (P.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
  · show P _ = f (-1)
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.source
  · show P _ = g 1
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.target
  · intro t _
    have hmem : P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)) ∈ Set.range P := ⟨_, rfl⟩
    rw [hP, Path.trans_range] at hmem
    have hr1 : Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := pathOfPiece_range hf
    have hr2 : Set.range ((pathOfPiece hg).cast hchain rfl) = g '' Icc (-1:ℝ) 1 := by
      simp only [Path.cast_coe]; exact pathOfPiece_range hg
    rw [hr1, hr2] at hmem
    exact hmem

theorem concatPath3 {f g h : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hh : ContinuousOn h (Icc (-1:ℝ) 1))
    (hfg : f 1 = g (-1)) (hgh : g 1 = h (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = h 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 ∪ h '' Icc (-1:ℝ) 1 := by
  obtain ⟨c2, hc2cont, hc2a, hc2b, hc2mem⟩ := concatPath2 hf hg hfg
  obtain ⟨c3, hc3cont, hc3a, hc3b, hc3mem⟩ :=
    concatPath2 hc2cont hh (by rw [hc2b]; exact hgh)
  refine ⟨c3, hc3cont, by rw [hc3a, hc2a], hc3b, fun t ht => ?_⟩
  rcases hc3mem t ht with hin | hin
  · obtain ⟨u, hu, huc⟩ := hin
    exact Set.mem_union_left _ (huc ▸ hc2mem u hu)
  · exact Set.mem_union_right _ hin

theorem concatPath5 {f1 f2 f3 f4 f5 : ℝ → Plane}
    (h1 : ContinuousOn f1 (Icc (-1:ℝ) 1)) (h2 : ContinuousOn f2 (Icc (-1:ℝ) 1))
    (h3 : ContinuousOn f3 (Icc (-1:ℝ) 1)) (h4 : ContinuousOn f4 (Icc (-1:ℝ) 1))
    (h5 : ContinuousOn f5 (Icc (-1:ℝ) 1))
    (c12 : f1 1 = f2 (-1)) (c23 : f2 1 = f3 (-1)) (c34 : f3 1 = f4 (-1))
    (c45 : f4 1 = f5 (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f1 (-1) ∧ c 1 = f5 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ ((((f1 '' Icc (-1:ℝ) 1 ∪ f2 '' Icc (-1:ℝ) 1) ∪ f3 '' Icc (-1:ℝ) 1)
          ∪ f4 '' Icc (-1:ℝ) 1) ∪ f5 '' Icc (-1:ℝ) 1) := by
  obtain ⟨c123, hc123cont, hc123a, hc123b, hc123mem⟩ := concatPath3 h1 h2 h3 c12 c23
  obtain ⟨c45, hc45cont, hc45a, hc45b, hc45mem⟩ := concatPath2 h4 h5 c45
  obtain ⟨c, hccont, hca, hcb, hcmem⟩ :=
    concatPath2 hc123cont hc45cont (by rw [hc123b, hc45a]; exact c34)
  refine ⟨c, hccont, by rw [hca, hc123a], by rw [hcb, hc45b], fun t ht => ?_⟩
  rcases hcmem t ht with hin | hin
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc123mem u hu
    rw [hue] at hmem
    exact Or.inl (Or.inl hmem)
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc45mem u hu
    rw [hue] at hmem
    rcases hmem with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem exists_ymin_Jn_axis {J_n : Set Plane} (hJncl : IsClosed J_n)
    (hcpt : IsCompact J_n) {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0) :
    ∃ m ∈ J_n, m 0 = 0 ∧ ∀ p ∈ J_n, p 0 = 0 → m 1 ≤ p 1 := by
  set Jm : Set Plane := {p ∈ J_n | p 0 = 0} with hJm
  have hsub : Jm ⊆ J_n := fun p hp => hp.1
  have hcl : IsClosed Jm :=
    hJncl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hJmcpt : IsCompact Jm := hcpt.of_isClosed_subset hcl hsub
  have hne : Jm.Nonempty := ⟨l, hlJn, hl0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨m, hmJm, hmmin⟩ :=
    hJmcpt.exists_isMinOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  exact ⟨m, hmJm.1, hmJm.2, fun p hpJn hp0 => hmmin (show p ∈ Jm from ⟨hpJn, hp0⟩)⟩

theorem ms_meets_Js (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (_hcont : Continuous r) (_hinj : Injective r)
    (hmr : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hpr : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane}
    (hUnion : J_n ∪ J_s = range r)
    (hInter : J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]})
    (eJs : ↥J_s ≃ₜ unitInterval)
    (hpcJn : IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}))
    {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0)
    (hlmax : ∀ q ∈ range r, q 0 = 0 → q 1 ≤ l 1)
    {m : Plane} (hmJn : m ∈ J_n) (hm0 : m 0 = 0) :
    ∃ w ∈ J_s, w 0 = 0 ∧ w 1 ≤ m 1 := by
  set a : Plane := !₂[(-1:ℝ), 0] with ha_def
  set b : Plane := !₂[(1:ℝ), 0] with hb_def

  obtain ⟨s, hs0, hs1⟩ : ∃ s : Plane, s 0 = 0 ∧ s 1 = -2 :=
    ⟨!₂[(0:ℝ), -2], by simp, by simp⟩
  obtain ⟨nn, hn0, hn1⟩ : ∃ nn : Plane, nn 0 = 0 ∧ nn 1 = 2 :=
    ⟨!₂[(0:ℝ), 2], by simp, by simp⟩
  have ha0 : a 0 = -1 := by simp [ha_def]
  have hb0 : b 0 = 1 := by simp [hb_def]

  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hrect := normalized_subset_rectangle hmr hpr hfar
  have hmrange : m ∈ range r := hJnr hmJn
  have hlrange : l ∈ range r := hJnr hlJn
  have hm1lb : (-2 : ℝ) ≤ m 1 := (hrect hmrange).2.1
  have hm1ub : m 1 ≤ 2 := (hrect hmrange).2.2
  have hl1lb : (-2 : ℝ) ≤ l 1 := (hrect hlrange).2.1
  have hl1ub : l 1 ≤ 2 := (hrect hlrange).2.2

  have haJs : a ∈ J_s := by
    have : a ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert _ _
    exact this.2
  have hbJs : b ∈ J_s := by
    have : b ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJs : JoinedIn J_s a b := arc_joinedIn eJs haJs hbJs
  have hJsrect : J_s ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} :=
    hJsr.trans hrect

  have hmab : m ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hlab : l ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hl0, ha0, hb0] at hc; norm_num at hc)
  by_contra hcon
  push Not at hcon

  set f1 : ℝ → Plane := fun t => s + ((t + 1) / 2) • (m - s) with hf1def
  set f3 : ℝ → Plane := fun t => l + ((t + 1) / 2) • (nn - l) with hf3def
  obtain ⟨f2, hf2cont, hf2m, hf2l, hf2mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hf1cont : ContinuousOn f1 (Icc (-1:ℝ) 1) := (by fun_prop : Continuous f1).continuousOn
  have hf3cont : ContinuousOn f3 (Icc (-1:ℝ) 1) := (by fun_prop : Continuous f3).continuousOn
  have hf1_1 : f1 1 = m := by simp [hf1def]
  have hf1_m1 : f1 (-1) = s := by simp [hf1def]
  have hf3_1 : f3 1 = nn := by simp [hf3def]
  have hf3_m1 : f3 (-1) = l := by simp [hf3def]
  have hf1f2 : f1 1 = f2 (-1) := by rw [hf1_1, hf2m]
  have hf2f3 : f2 1 = f3 (-1) := by rw [hf2l, hf3_m1]
  obtain ⟨c, hccont, hcs, hcn, hcmem⟩ := concatPath3 hf1cont hf2cont hf3cont hf1f2 hf2f3

  have hcm1 : c (-1) 1 = -2 := by rw [hcs, hf1_m1]; exact hs1
  have hcn1 : c 1 1 = 2 := by rw [hcn, hf3_1]; exact hn1

  have hf1x : ∀ t, f1 t 0 = 0 := fun t => by simp [hf1def, hs0, hm0]
  have hf3x : ∀ t, f3 t 0 = 0 := fun t => by simp [hf3def, hl0, hn0]
  have hf1y_le : ∀ t ∈ Icc (-1:ℝ) 1, f1 t 1 ≤ m 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf1y_ge : ∀ t ∈ Icc (-1:ℝ) 1, (-2:ℝ) ≤ f1 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf3y_ge : ∀ t ∈ Icc (-1:ℝ) 1, l 1 ≤ f3 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1ub]
  have hf3y_le : ∀ t ∈ Icc (-1:ℝ) 1, f3 t 1 ≤ 2 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1lb, hl1ub]
  have hbound : ∀ z ∈ (f1 '' Icc (-1:ℝ) 1 ∪ f2 '' Icc (-1:ℝ) 1) ∪ f3 '' Icc (-1:ℝ) 1,
      z 0 ∈ Icc (-1:ℝ) 1 ∧ z 1 ∈ Icc (-2:ℝ) 2 := by
    rintro z ((⟨t1, ht1, rfl⟩ | ⟨t2, ht2, rfl⟩) | ⟨t3, ht3, rfl⟩)
    · exact ⟨by rw [hf1x]; norm_num,
        mem_Icc.2 ⟨hf1y_ge t1 ht1, le_trans (hf1y_le t1 ht1) hm1ub⟩⟩
    · exact hrect (hJnr (hf2mem t2 ht2).1)
    · exact ⟨by rw [hf3x]; norm_num,
        mem_Icc.2 ⟨le_trans hl1lb (hf3y_ge t3 ht3), hf3y_le t3 ht3⟩⟩
  have hcE : ∀ t ∈ Icc (-1:ℝ) 1, c t 0 ∈ Icc (-1:ℝ) 1 ∧ c t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hbound (c t) (hcmem t ht)

  obtain ⟨t, ht, hctJs⟩ :=
    vertical_meets_arc hbr hJsrect hJoinJs hccont hcE hcm1 hcn1
  rcases hcmem t ht with (⟨t1, ht1, ht1e⟩ | ⟨t2, ht2, ht2e⟩) | ⟨t3, ht3, ht3e⟩
  ·
    have hct0 : c t 0 = 0 := by rw [← ht1e]; exact hf1x t1
    have hcty : c t 1 ≤ m 1 := by rw [← ht1e]; exact hf1y_le t1 ht1
    exact absurd (hcon (c t) hctJs hct0) (not_lt.2 hcty)
  ·
    have hctJn : c t ∈ J_n := ht2e ▸ (hf2mem t2 ht2).1
    have hctnab : c t ∉ ({a, b} : Set Plane) := ht2e ▸ (hf2mem t2 ht2).2
    have : c t ∈ J_n ∩ J_s := ⟨hctJn, hctJs⟩
    rw [hInter] at this
    exact hctnab this
  ·
    have hct0 : c t 0 = 0 := by rw [← ht3e]; exact hf3x t3
    have hcty_ge : l 1 ≤ c t 1 := by rw [← ht3e]; exact hf3y_ge t3 ht3
    have hcty_le : c t 1 ≤ l 1 := hlmax (c t) (hJsr hctJs) hct0
    have hcty : c t 1 = l 1 := le_antisymm hcty_le hcty_ge
    have hctl : c t = l := by ext i; fin_cases i <;> simp [hct0, hl0, hcty]
    have hlnJs : l ∉ J_s := by
      intro h
      have : l ∈ J_n ∩ J_s := ⟨hlJn, h⟩
      rw [hInter] at this; exact hlab this
    exact hlnJs (hctl ▸ hctJs)

theorem exists_construction_points (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ (J_n J_s : Set Plane) (l m p q z₀ : Plane),
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} ∧
      IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      (l ∈ J_n ∧ l 0 = 0 ∧ ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1) ∧
      (m ∈ J_n ∧ m 0 = 0 ∧ ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1) ∧
      (p ∈ J_s ∧ p 0 = 0 ∧ p 1 ≤ m 1 ∧ ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1) ∧
      (q ∈ J_s ∧ q 0 = 0 ∧ ∀ w ∈ J_s, w 0 = 0 → q 1 ≤ w 1) ∧
      z₀ = !₂[(0:ℝ), (m 1 + p 1) / 2] ∧
      m 1 ≤ l 1 ∧ q 1 ≤ p 1 ∧ p 1 ≤ z₀ 1 ∧ z₀ 1 ≤ m 1 ∧
      IsPathConnected (J_s \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) ∧
      JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := by
  obtain ⟨J_n, J_s, hJncl, hJscl, hUnion, hInter, ⟨eJn⟩, ⟨eJs⟩, hpcJn, hpcJs,
    l, hlr, hl0, hlmax, hlJn⟩ := jordan_arcs hbr hcont hinj hm hp hfar
  have hcptr : IsCompact (range r) := jordanCurve_isCompact r hcont
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hJncpt : IsCompact J_n := hcptr.of_isClosed_subset hJncl hJnr
  have hJscpt : IsCompact J_s := hcptr.of_isClosed_subset hJscl hJsr

  obtain ⟨m, hmJn, hm0, hmmin⟩ := exists_ymin_Jn_axis hJncl hJncpt hlJn hl0

  obtain ⟨w₀, hw₀Js, hw₀0, hw₀m⟩ :=
    ms_meets_Js hbr hcont hinj hm hp hfar hUnion hInter eJs hpcJn hlJn hl0 hlmax hmJn hm0

  set Sp : Set Plane := {w ∈ J_s | w 0 = 0 ∧ w 1 ≤ m 1} with hSpdef
  have hSpcl : IsClosed Sp := by
    have hEq : Sp = (J_s ∩ {w : Plane | w 0 = 0}) ∩ {w : Plane | w 1 ≤ m 1} := by
      ext w
      constructor
      · rintro ⟨hJ, h0, hle⟩; exact ⟨⟨hJ, h0⟩, hle⟩
      · rintro ⟨⟨hJ, h0⟩, hle⟩; exact ⟨hJ, h0, hle⟩
    rw [hEq]
    exact (hJscl.inter (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hSpcpt : IsCompact Sp := hJscpt.of_isClosed_subset hSpcl (fun w hw => hw.1)
  obtain ⟨p, hpSp, hpmax⟩ := hSpcpt.exists_isMaxOn ⟨w₀, hw₀Js, hw₀0, hw₀m⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn

  set Sq : Set Plane := {w ∈ J_s | w 0 = 0} with hSqdef
  have hSqcl : IsClosed Sq :=
    hJscl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hSqcpt : IsCompact Sq := hJscpt.of_isClosed_subset hSqcl (fun w hw => hw.1)
  obtain ⟨q, hqSq, hqmin⟩ := hSqcpt.exists_isMinOn ⟨w₀, hw₀Js, hw₀0⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn

  have hpm : p 1 ≤ m 1 := hpSp.2.2
  have hml : m 1 ≤ l 1 := hlmax m (hJnr hmJn) hm0
  have hqp : q 1 ≤ p 1 := hqmin ⟨hpSp.1, hpSp.2.1⟩
  have haJn : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.1
  have hbJn : (!₂[(1:ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.1
  have haJs : (!₂[(-1:ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.2
  have hbJs : (!₂[(1:ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJn : JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := arc_joinedIn eJn haJn hbJn
  have hJoinJs : JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := arc_joinedIn eJs haJs hbJs
  refine ⟨J_n, J_s, l, m, p, q, !₂[(0:ℝ), (m 1 + p 1) / 2], hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩,
    ⟨hpSp.1, hpSp.2.1, hpm, fun w hwJs hw0 hwm => hpmax ⟨hwJs, hw0, hwm⟩⟩,
    ⟨hqSq.1, hqSq.2, fun w hwJs hw0 => hqmin ⟨hwJs, hw0⟩⟩, rfl, hml, hqp, ?_, ?_,
    hpcJs, hJoinJn, hJoinJs⟩
  · rw [show (!₂[(0:ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]
  · rw [show (!₂[(0:ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]

theorem exists_first_exit {α : ℝ → Plane} {O C : Set Plane}
    (hO : IsOpen O) (hC : IsClosed C) (hOC : O ⊆ C)
    (hcont : ContinuousOn α (Icc (0:ℝ) 1))
    (h0 : α 0 ∈ O) (h1 : α 1 ∉ C) :
    ∃ tw ∈ Ioc (0:ℝ) 1, α tw ∈ C ∧ α tw ∉ O ∧ ∀ u ∈ Ico (0:ℝ) tw, α u ∈ O := by
  set S : Set ℝ := {t ∈ Icc (0:ℝ) 1 | α t ∉ O} with hSdef

  have hScl : IsClosed S := by
    have hEq : S = Icc (0:ℝ) 1 ∩ α ⁻¹' Oᶜ := by
      ext t; simp only [hSdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    rw [hEq]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty :=
    ⟨1, ⟨by norm_num, fun h => h1 (hOC h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set tw := sInf S with htw
  have htwS : tw ∈ S := hScl.csInf_mem hSne hSbdd
  have htw01 : tw ∈ Icc (0:ℝ) 1 := htwS.1
  have htwO : α tw ∉ O := htwS.2

  have h0S : (0:ℝ) ∉ S := fun h => h.2 h0
  have htwpos : 0 < tw := lt_of_le_of_ne htw01.1 (fun h => h0S (h ▸ htwS))

  have hbelow : ∀ u ∈ Ico (0:ℝ) tw, α u ∈ O := by
    intro u hu
    by_contra hnot
    have huS : u ∈ S := ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hnot⟩
    exact absurd (csInf_le hSbdd huS) (not_le.2 hu.2)

  have htwC : α tw ∈ C := by
    have hT : IsClosed (Icc (0:ℝ) 1 ∩ α ⁻¹' C) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hsub : Ico (0:ℝ) tw ⊆ Icc (0:ℝ) 1 ∩ α ⁻¹' C := by
      intro u hu
      exact ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hOC (hbelow u hu)⟩
    have : tw ∈ Icc (0:ℝ) 1 ∩ α ⁻¹' C := by
      apply hT.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt htwpos)]
      exact ⟨htwpos.le, le_refl tw⟩
    exact this.2
  exact ⟨tw, ⟨htwpos, htw01.2⟩, htwC, htwO, hbelow⟩

theorem isPathConnected_vertSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
  have hfcont : Continuous (fun y : ℝ => (!₂[c, y] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun y : ℝ => (!₂[c, y] : Plane)) '' T = {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
    ext p
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 1, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

theorem isPathConnected_horizSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
  have hfcont : Continuous (fun x : ℝ => (!₂[x, c] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun x : ℝ => (!₂[x, c] : Plane)) '' T = {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
    ext p
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 0, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

theorem curve_boundary_axis
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ p ∈ range r, (p 0 = -1 ∨ p 0 = 1 ∨ p 1 = -2 ∨ p 1 = 2) → p 1 = 0 := by
  intro p hp' hbdry
  have hza : dist p (!₂[(-1:ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hm; nlinarith [dist_nonneg (x := p) (y := (!₂[(-1:ℝ),0] : Plane))]
  have hzb : dist p (!₂[(1:ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hp; nlinarith [dist_nonneg (x := p) (y := (!₂[(1:ℝ),0] : Plane))]
  rw [dist_sq_coord] at hza hzb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hza hzb
  rcases hbdry with h | h | h | h
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hzb]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hza]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 + 2)]
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 - 2)]

theorem exists_lower_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0:ℝ), -2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1:ℝ) 1 → p 1 ∈ Icc (-2:ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2) → p 1 < 0 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ico (-2:ℝ) 0} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ico (-2:ℝ) 0} with hRdef
  set Bot : Set Plane := {p : Plane | p 1 = -2 ∧ p 0 ∈ Icc (-1:ℝ) 1} with hBdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hBpc : IsPathConnected Bot :=
    isPathConnected_horizSeg (-2) ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1:ℝ), -2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have memBotL : (!₂[(-1:ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memBotR : (!₂[(1:ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1:ℝ), -2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have hLB : IsPathConnected (L ∪ Bot) := hLpc.union hBpc ⟨_, memL, memBotL⟩
  have hG : IsPathConnected ((L ∪ Bot) ∪ Rt) := hLB.union hRpc ⟨_, Or.inr memBotR, memR⟩
  refine ⟨(L ∪ Bot) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.2]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inl hpp.1))); linarith [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.2]
  · intro p hp0 hp1 hnint hpneg
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exact Or.inl (Or.inr ⟨le_antisymm (not_lt.mp h) hp1.1, hp0⟩)
      · exfalso; linarith [not_lt.mp h]

theorem exists_upper_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0:ℝ), 2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1:ℝ) 1 → p 1 ∈ Icc (-2:ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2) → 0 < p 1 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ioc (0:ℝ) 2} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ioc (0:ℝ) 2} with hRdef
  set Top : Set Plane := {p : Plane | p 1 = 2 ∧ p 0 ∈ Icc (-1:ℝ) 1} with hTdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hTpc : IsPathConnected Top :=
    isPathConnected_horizSeg 2 ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1:ℝ), 2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have memTopL : (!₂[(-1:ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memTopR : (!₂[(1:ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1:ℝ), 2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have hLT : IsPathConnected (L ∪ Top) := hLpc.union hTpc ⟨_, memL, memTopL⟩
  have hG : IsPathConnected ((L ∪ Top) ∪ Rt) := hLT.union hRpc ⟨_, Or.inr memTopR, memR⟩
  refine ⟨(L ∪ Top) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inr hpp.1))); linarith [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.1]
  · intro p hp0 hp1 hnint hppos
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exfalso; linarith [not_lt.mp h]
      · exact Or.inl (Or.inr ⟨le_antisymm hp1.2 (not_lt.mp h), hp0⟩)

private lemma off_axis_endpoints {x : Plane} (hx : x 0 = 0) :
    x ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h) <;>
    (have hc := congrArg (fun w : Plane => w 0) h; simp only [hx] at hc; norm_num at hc)

private lemma mul_unit_mem_Icc {tw u : ℝ} (htw : 0 ≤ tw) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    tw * u ∈ Icc (0:ℝ) tw := by
  rw [mem_Icc]
  refine ⟨mul_nonneg htw h0, ?_⟩
  calc tw * u ≤ tw * 1 := mul_le_mul_of_nonneg_left h1 htw
    _ = tw := mul_one tw

private lemma axis_segment {x y : Plane} (hx0 : x 0 = 0) (hy0 : y 0 = 0) (hxy : x 1 ≤ y 1) :
    ∃ g : ℝ → Plane, ContinuousOn g (Icc (-1:ℝ) 1) ∧ g (-1) = x ∧ g 1 = y ∧
      (∀ t, g t 0 = 0) ∧ ∀ t ∈ Icc (-1:ℝ) 1, g t 1 ∈ Icc (x 1) (y 1) := by
  refine ⟨fun t => x + ((t + 1) / 2) • (y - x),
    (by fun_prop : Continuous fun t : ℝ => x + ((t + 1) / 2) • (y - x)).continuousOn,
    by show x + (((-1:ℝ) + 1) / 2) • (y - x) = x; module,
    by show x + (((1:ℝ) + 1) / 2) • (y - x) = y; module,
    fun t => by simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hx0, hy0], ?_⟩
  intro t ht; rw [mem_Icc] at ht ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have h0 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  have hd : (0:ℝ) ≤ y 1 - x 1 := by linarith
  constructor
  · linarith [mul_nonneg h0 hd]
  · linarith [mul_le_mul_of_nonneg_right h1 hd]

private lemma isBounded_rectE :
    IsBounded {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} := by
  apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 3)).subset
  intro z hz
  rw [Metric.mem_closedBall]
  have hz1 := hz.1; have hz2 := hz.2; rw [mem_Icc] at hz1 hz2
  have hsq : dist z (0:Plane) ^ 2 ≤ 9 := by
    rw [dist_sq_coord, show (0:Plane) 0 = 0 from by simp, show (0:Plane) 1 = 0 from by simp]
    nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
  nlinarith [dist_nonneg (x := z) (y := (0:Plane)), hsq]

private lemma isOpen_rectO :
    IsOpen {w : Plane | w 0 ∈ Ioo (-1:ℝ) 1 ∧ w 1 ∈ Ioo (-2:ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Ioo (-1:ℝ) 1 ∧ w 1 ∈ Ioo (-2:ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Ioo (-1:ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Ioo (-2:ℝ) 2 := by
    ext w; simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))

private lemma isClosed_rectE :
    IsClosed {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Icc (-1:ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Icc (-2:ℝ) 2 := by
    ext w; simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isClosed_Icc.preimage (by fun_prop)).inter (isClosed_Icc.preimage (by fun_prop))

private lemma axis_zero_mem_range {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    {x : Plane} (hxIcc : x 0 ∈ Icc (-1:ℝ) 1)
    (hxO : ¬(x 0 ∈ Ioo (-1:ℝ) 1 ∧ x 1 ∈ Ioo (-2:ℝ) 2))
    (hx1 : x 1 = 0) : x ∈ range r := by
  have hnotIoo0 : x 0 ∉ Ioo (-1:ℝ) 1 := fun hIoo =>
    hxO ⟨hIoo, by rw [hx1, mem_Ioo]; constructor <;> norm_num⟩
  rw [mem_Ioo, not_and_or] at hnotIoo0
  rcases hnotIoo0 with h | h
  · have hx : x 0 = -1 := le_antisymm (not_lt.mp h) hxIcc.1
    rw [show x = !₂[(-1:ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hm
  · have hx : x 0 = 1 := le_antisymm hxIcc.2 (not_lt.mp h)
    rw [show x = !₂[(1:ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hp

private lemma step_A_case_low (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane))
    (hpcJn : IsPathConnected (J_n \ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane)))
    (hJoinJs : JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {l m p z₀ : Plane}
    (hlJn : l ∈ J_n) (hl0 : l 0 = 0) (hlmax : ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1)
    (hmJn : m ∈ J_n) (hm0 : m 0 = 0)
    (hpJs : p ∈ J_s) (hpmax : ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0:ℝ) tw, α u 0 ∈ Icc (-1:ℝ) 1 ∧ α u 1 ∈ Icc (-2:ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1:ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2:ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1:ℝ) 1 ∧ α tw 1 ∈ Ioo (-2:ℝ) 2))
    (hwneg : α tw 1 < 0) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hmab := off_axis_endpoints hm0
  have hlab := off_axis_endpoints hl0
  have hlE1 : l 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hlJn)).2
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2
  have hz₀1lb : (-2:ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Glo, hGloPC, hsGlo, hGloSub, hGloAvoid, hGloFrom⟩ :=
    exists_lower_boundary_path hm hp hfar
  have hwGlo : α tw ∈ Glo := hGloFrom (α tw) hwC0 hwC1 hwO hwneg

  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1mem⟩ :=
    arc_path (hGloPC.joinedIn (!₂[(0:ℝ), -2]) hsGlo (α tw) hwGlo)

  set g2 : ℝ → Plane := fun t => α (tw * (1 - t) / 2) with hg2def
  have hg2cont : ContinuousOn g2 (Icc (-1:ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (1 - t) / 2)).continuousOn
  have hg2a : g2 (-1) = α tw := by show α (tw * (1 - (-1)) / 2) = α tw; congr 1; ring
  have hg2b : g2 1 = z₀ := by
    show α (tw * (1 - 1) / 2) = z₀; rw [show tw * (1 - 1) / 2 = (0:ℝ) from by ring, hα0]
  have hg2arg : ∀ t ∈ Icc (-1:ℝ) 1, tw * (1 - t) / 2 ∈ Icc (0:ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.2]) (by linarith [ht.1])

  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hz₀0 hm0 hz₀m_lt.le
  have hg3missJs : ∀ t ∈ Icc (-1:ℝ) 1, g3 t ∉ J_s := by
    intro t ht hJs
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hpmax (g3 t) hJs (hg3x t) hy.2
    linarith [hy.1, hpz₀_lt]

  obtain ⟨g4, hg4cont, hg4a, hg4b, hg4mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hg4missJs : ∀ t ∈ Icc (-1:ℝ) 1, g4 t ∉ J_s := by
    intro t ht hJs
    have hg4 := hg4mem t ht
    have hmem : g4 t ∈ J_n ∩ J_s := ⟨hg4.1, hJs⟩
    rw [hInter] at hmem; exact hg4.2 hmem

  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5x, hg5y⟩ :=
    axis_segment hl0 (show (!₂[(0:ℝ), 2] : Plane) 0 = 0 from by simp) (by rw [hn1]; exact hlE1.2)
  have hg5missJs : ∀ t ∈ Icc (-1:ℝ) 1, g5 t ∉ J_s := by
    intro t ht hJs
    have hy := hg5y t ht; rw [mem_Icc] at hy
    have hle := hlmax (g5 t) (hJsr hJs) (hg5x t)
    have heq : g5 t 1 = l 1 := le_antisymm hle hy.1
    have hgl : g5 t = l := by ext i; fin_cases i <;> simp [hg5x t, hl0, heq]
    rw [hgl] at hJs
    have hmem : l ∈ J_n ∩ J_s := ⟨hlJn, hJs⟩
    rw [hInter] at hmem; exact hlab hmem

  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1:ℝ) 1, V t 0 ∈ Icc (-1:ℝ) 1 ∧ V t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGloSub (hg1mem u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg2arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hz₀1lb hy.1, le_trans hy.2 hmE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hg4mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg5y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg5x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hlE1.1 hy.1, hy.2⟩⟩
  have hVmiss : ∀ t ∈ Icc (-1:ℝ) 1, V t ∉ J_s := by
    intro t ht hJs
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hGloAvoid (g1 u) (hg1mem u hu) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hαnr (tw * (1 - u) / 2) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg3missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg4missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg5missJs u hu hJs
  have hJsrect : J_s ⊆ {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} :=
    fun w hw => hErect (hJsr hw)
  obtain ⟨t, ht, htJs⟩ := vertical_meets_arc hbr hJsrect hJoinJs hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJs

private lemma step_A_case_high (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane))
    (hpcJs : IsPathConnected (J_s \ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane)))
    (hJoinJn : JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {m p q z₀ : Plane}
    (hmJn : m ∈ J_n) (_hm0 : m 0 = 0) (hmmin : ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1)
    (hpJs : p ∈ J_s) (hp0 : p 0 = 0)
    (hqJs : q ∈ J_s) (hq0 : q 0 = 0) (hqm : q 1 < m 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0:ℝ) tw, α u 0 ∈ Icc (-1:ℝ) 1 ∧ α u 1 ∈ Icc (-2:ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1:ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2:ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1:ℝ) 1 ∧ α tw 1 ∈ Ioo (-2:ℝ) 2))
    (hwpos : 0 < α tw 1) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hqab := off_axis_endpoints hq0
  have hpab := off_axis_endpoints hp0
  have hqE1 : q 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hqJs)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Gup, hGupPC, hnGup, hGupSub, hGupAvoid, hGupFrom⟩ :=
    exists_upper_boundary_path hm hp hfar
  have hwGup : α tw ∈ Gup := hGupFrom (α tw) hwC0 hwC1 hwO hwpos

  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1x, hg1y⟩ :=
    axis_segment (show (!₂[(0:ℝ), -2] : Plane) 0 = 0 from by simp) hq0 (by rw [hs1]; exact hqE1.1)
  have hg1missJn : ∀ t ∈ Icc (-1:ℝ) 1, g1 t ∉ J_n := by
    intro t ht hJn
    have hy := hg1y t ht; rw [mem_Icc] at hy
    have := hmmin (g1 t) hJn (hg1x t)
    linarith [hy.2, hqm]

  obtain ⟨g2, hg2cont, hg2a, hg2b, hg2mem⟩ :=
    arc_path (hpcJs.joinedIn q ⟨hqJs, hqab⟩ p ⟨hpJs, hpab⟩)
  have hg2missJn : ∀ t ∈ Icc (-1:ℝ) 1, g2 t ∉ J_n := by
    intro t ht hJn
    have hg2' := hg2mem t ht
    have hmem : g2 t ∈ J_n ∩ J_s := ⟨hJn, hg2'.1⟩
    rw [hInter] at hmem; exact hg2'.2 hmem

  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hp0 hz₀0 hpz₀_lt.le
  have hg3missJn : ∀ t ∈ Icc (-1:ℝ) 1, g3 t ∉ J_n := by
    intro t ht hJn
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hmmin (g3 t) hJn (hg3x t)
    linarith [hy.2, hz₀m_lt]

  set g4 : ℝ → Plane := fun t => α (tw * (t + 1) / 2) with hg4def
  have hg4cont : ContinuousOn g4 (Icc (-1:ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (t + 1) / 2)).continuousOn
  have hg4a : g4 (-1) = z₀ := by
    show α (tw * ((-1) + 1) / 2) = z₀; rw [show tw * ((-1) + 1) / 2 = (0:ℝ) from by ring, hα0]
  have hg4b : g4 1 = α tw := by show α (tw * (1 + 1) / 2) = α tw; congr 1; ring
  have hg4arg : ∀ t ∈ Icc (-1:ℝ) 1, tw * (t + 1) / 2 ∈ Icc (0:ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.1]) (by linarith [ht.2])

  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5mem⟩ :=
    arc_path (hGupPC.joinedIn (α tw) hwGup (!₂[(0:ℝ), 2]) hnGup)
  have hg5missJn : ∀ t ∈ Icc (-1:ℝ) 1, g5 t ∉ J_n := by
    intro t ht hJn; exact hGupAvoid (g5 t) (hg5mem t ht) (hJnr hJn)

  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1:ℝ) 1, V t 0 ∈ Icc (-1:ℝ) 1 ∧ V t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg1y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg1x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨hy.1, le_trans hy.2 hqE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hg2mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hpE1.1 hy.1, le_trans hy.2 hz₀1ub⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg4arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGupSub (hg5mem u hu)
  have hVmiss : ∀ t ∈ Icc (-1:ℝ) 1, V t ∉ J_n := by
    intro t ht hJn
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg1missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg2missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg3missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn
      exact hαnr (tw * (u + 1) / 2) (hJnr hJn)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg5missJn u hu hJn
  have hJnrect : J_n ⊆ {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} :=
    fun w hw => hErect (hJnr hw)
  obtain ⟨t, ht, htJn⟩ := vertical_meets_arc hbr hJnrect hJoinJn hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJn

theorem step_A_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar

  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2

  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith

  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  refine ⟨z₀, hz₀c, ?_⟩

  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} with hEdef
  set O : Set Plane := {p : Plane | p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2} with hOdef
  have hEbdd : IsBounded E := by rw [hEdef]; exact isBounded_rectE
  have hOopen : IsOpen O := by rw [hOdef]; exact isOpen_rectO
  have hEclosed : IsClosed E := by rw [hEdef]; exact isClosed_rectE
  have hOE : O ⊆ E := fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hz₀O : z₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [mem_Ioo, hz₀0]; constructor <;> norm_num
    · rw [mem_Ioo, hz₀1e]; exact ⟨by linarith [hpE1.1, hpm_lt], by linarith [hmE1.2, hpm_lt]⟩

  by_contra hUunb
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUeq
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  have hUpc : IsPathConnected U := isPathConnected_component r hcont hz₀c
  have hUnotsub : ¬ U ⊆ E := fun h => hUunb (hEbdd.subset h)
  obtain ⟨y, hyU, hyE⟩ := Set.not_subset.mp hUnotsub

  have hJoinU : JoinedIn U z₀ y := hUpc.joinedIn z₀ hz₀U y hyU
  set α : ℝ → Plane := fun t => hJoinU.somePath (Set.projIcc (0:ℝ) 1 (by norm_num) t) with hαdef
  have hαcont : Continuous α := hJoinU.somePath.continuous.comp continuous_projIcc
  have hα0 : α 0 = z₀ := by
    show hJoinU.somePath _ = z₀
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) 0 = 0 from Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.source
  have hα1 : α 1 = y := by
    show hJoinU.somePath _ = y
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) 1 = 1 from Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.target
  have hαU : ∀ t : ℝ, α t ∈ U := fun t => hJoinU.somePath_mem _

  obtain ⟨tw, htw, hwC, hwO, hbelow⟩ :=
    exists_first_exit hOopen hEclosed hOE hαcont.continuousOn (by rw [hα0]; exact hz₀O)
      (by rw [hα1]; exact hyE)
  have hαE : ∀ u ∈ Icc (0:ℝ) tw, α u ∈ E := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hwC
    · exact hOE (hbelow u ⟨hu.1, h⟩)
  have hwnr : α tw ∉ range r := hUsub (hαU tw)

  have hw1ne : α tw 1 ≠ 0 := fun hzero =>
    hwnr (axis_zero_mem_range hm hp hwC.1 hwO hzero)
  rcases lt_or_gt_of_ne hw1ne with hwneg | hwpos
  · exact step_A_case_low hbr hm hp hfar hJnr hJsr hInter hpcJn hJoinJs
      hlJn hl0 hlmax hmJn hm0 hpJs hpmax hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwneg
  · exact step_A_case_high hbr hm hp hfar hJnr hJsr hInter hpcJs hJoinJn
      hmJn hm0 hmmin hpJs hp0 hqJs hq0 hqm hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwpos

theorem step_A_exists_bounded (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨a, ha, b, hb, hfar, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0:ℝ) < 2 / dist a b := by positivity

  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]

  have hm' : (!₂[(-1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b := by
          exact mul_le_mul_of_nonneg_left (hfar z hz w hw) hcpos.le
      _ = 2 := by field_simp
  obtain ⟨x, hx, hxb⟩ := step_A_normalized hbr hr'cont hr'inj hm' hp' hfar'

  rw [hrange] at hx hxb

  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  rw [himg] at hx hxb
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  refine ⟨x₀, hx₀, ?_⟩

  have hcc : connectedComponentIn ((T : Plane → Plane) '' (range r)ᶜ) (T x₀)
      = T '' connectedComponentIn (range r)ᶜ x₀ :=
    (T.image_connectedComponentIn hx₀).symm
  rw [hcc] at hxb
  exact (isBounded_image_scaling hcpos hscale _).mp hxb

private lemma norm_axis_pt (y : ℝ) : ‖(!₂[(0:ℝ), y] : Plane)‖ = |y| := by
  have e0 : (!₂[(0:ℝ), y] : Plane) 0 = 0 := by simp
  have e1 : (!₂[(0:ℝ), y] : Plane) 1 = y := by simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1]
  simp [Real.sqrt_sq_eq_abs]

private lemma axis_ray_up_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) 1 = |c| + |M| + 1 := by simp
  have hmem : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Ioi, hy1]; linarith [le_abs_self c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

private lemma axis_ray_down_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) 1 = -(|c| + |M| + 1) := by simp
  have hmem : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Iio, hy1]; linarith [neg_abs_le c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

private lemma isPreconnected_rect_compl :
    IsPreconnected {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)} := by
  have cA : Convex ℝ {v : Plane | v 0 ∈ Iio (-1:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cB : Convex ℝ {v : Plane | v 0 ∈ Ioi (1:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cC : Convex ℝ {v : Plane | v 1 ∈ Iio (-2:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  have cD : Convex ℝ {v : Plane | v 1 ∈ Ioi (2:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear

  have mAD_A : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Iio (-1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio]; norm_num
  have mAD_D : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mB_D : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mB_B : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mC_B : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mC_C : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 1 ∈ Iio (-2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio]; norm_num
  have hAD : IsPreconnected ({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)}) :=
    cA.isPreconnected.union _ mAD_A mAD_D cD.isPreconnected
  have hADB : IsPreconnected (({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) :=
    hAD.union _ (Or.inr mB_D) mB_B cB.isPreconnected
  have hADBC : IsPreconnected ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) :=
    hADB.union _ (Or.inr mC_B) mC_C cC.isPreconnected
  have hEq : {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)}
      = ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) := by
    ext v
    simp only [mem_setOf_eq, mem_union, mem_Icc, mem_Iio, mem_Ioi, not_and_or, not_le]
    tauto
  rw [hEq]; exact hADBC

private noncomputable def segP (P Q : Plane) : ℝ → Plane := fun t => P + ((t + 1) / 2) • (Q - P)

private lemma segP_cont (P Q : Plane) : Continuous (segP P Q) := by unfold segP; fun_prop

private lemma segP_neg1 (P Q : Plane) : segP P Q (-1) = P := by simp [segP]

private lemma segP_one (P Q : Plane) : segP P Q 1 = Q := by simp [segP]

private lemma segP_coord (P Q : Plane) (t : ℝ) (i : Fin 2) :
    segP P Q t i = P i + ((t + 1) / 2) * (Q i - P i) := by
  simp only [segP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

private lemma segP_dist_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) P ≤ dist Q P := by
  have hs : |(t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) P = |(t + 1) / 2| * dist Q P := by
    rw [segP, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |(t + 1) / 2| * dist Q P ≤ 1 * dist Q P :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist Q P := one_mul _

private lemma segP_dist_le' (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) Q ≤ dist P Q := by
  have hs : |1 - (t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) Q = |1 - (t + 1) / 2| * dist P Q := by
    rw [segP, dist_eq_norm,
      show P + ((t + 1) / 2) • (Q - P) - Q = (1 - (t + 1) / 2) • (P - Q) from by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |1 - (t + 1) / 2| * dist P Q ≤ 1 * dist P Q :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist P Q := one_mul _

private lemma segP_coord_mem_Icc {P Q : Plane} (i : Fin 2) {lo hi : ℝ}
    (hP : P i ∈ Icc lo hi) (hQ : Q i ∈ Icc lo hi) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    segP P Q t i ∈ Icc lo hi := by
  rw [mem_Icc] at hP hQ ht
  rw [segP_coord, mem_Icc]
  have hs0 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have hs1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.1] : (0:ℝ) ≤ Q i - lo),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.1] : (0:ℝ) ≤ P i - lo)]
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.2] : (0:ℝ) ≤ hi - Q i),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.2] : (0:ℝ) ≤ hi - P i)]

theorem step_B_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar

  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have ha0 : (!₂[(-1:ℝ), 0] : Plane) 0 = -1 := by simp
  have ha1 : (!₂[(-1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hb0 : (!₂[(1:ℝ), 0] : Plane) 0 = 1 := by simp
  have hb1 : (!₂[(1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hs0 : (!₂[(0:ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0:ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmr : m ∈ range r := hJnr hmJn
  have hlr : l ∈ range r := hJnr hlJn
  have hpr : p ∈ range r := hJsr hpJs
  have hqr : q ∈ range r := hJsr hqJs
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect hmr).2
  have hlE1 : l 1 ∈ Icc (-2:ℝ) 2 := (hErect hlr).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect hpr).2
  have hqE1 : q 1 ∈ Icc (-2:ℝ) 2 := (hErect hqr).2
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  have hz₀1lb : (-2:ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hmab : m ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hm0] at hc; norm_num at hc)
  have hlab : l ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hl0] at hc; norm_num at hc)
  have hqab : q ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hq0] at hc; norm_num at hc)
  have hpab : p ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hp0] at hc; norm_num at hc)
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)

  have hIcc0x : (0:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc0y : (0:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm1x : (-1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc1x : (1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num

  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUdef
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} with hEdef

  set Mid : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} with hMiddef
  have hMidPC : IsPathConnected Mid :=
    isPathConnected_vertSeg 0 ((convex_Ioo (p 1) (m 1)).isPathConnected (Set.nonempty_Ioo.mpr hpm_lt))
  have hMidc : Mid ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (hmmin v h hv0) (not_le.2 hv1.2)
    · exact absurd (hpmax v h hv0 hv1.2.le) (not_le.2 hv1.1)
  have hz₀Mid : z₀ ∈ Mid :=
    ⟨hz₀0, by rw [hz₀1e]; exact ⟨by linarith [hpm_lt], by linarith [hpm_lt]⟩⟩
  have hMidU : Mid ⊆ U :=
    hMidPC.isConnected.isPreconnected.subset_connectedComponentIn hz₀Mid hMidc

  set RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} with hRayNdef
  have hRayNPC : IsPathConnected RayN :=
    isPathConnected_vertSeg 0 ((convex_Ioi (l 1)).isPathConnected Set.nonempty_Ioi)
  have hRayNc : RayN ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr; exact absurd (hlmax v hvr hv0) (not_le.2 hv1)
  set RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} with hRaySdef
  have hRaySPC : IsPathConnected RayS :=
    isPathConnected_vertSeg 0 ((convex_Iio (q 1)).isPathConnected Set.nonempty_Iio)
  have hRaySc : RayS ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (le_trans (le_trans hqp hpm) (hmmin v h hv0)) (not_le.2 hv1)
    · exact absurd (hqmin v h hv0) (not_le.2 hv1)

  have KEY : ∀ w ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ w) →
      connectedComponentIn (range r)ᶜ w = U := by
    intro w hw hwb
    by_contra hWne
    set W : Set Plane := connectedComponentIn (range r)ᶜ w with hWdef
    have hWsub : W ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
    have hwW : w ∈ W := mem_connectedComponentIn hw
    have hWpc : IsPathConnected W := isPathConnected_component r hcont hw

    have hWU_disj : Disjoint W U := by
      rw [Set.disjoint_left]
      intro v hvW hvU
      apply hWne
      rw [hWdef, connectedComponentIn_eq (hWdef ▸ hvW), hUdef]
      exact (connectedComponentIn_eq (hUdef ▸ hvU)).symm

    have compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn (range r)ᶜ v = W := by
      intro v hvW; rw [hWdef]; exact (connectedComponentIn_eq (hWdef ▸ hvW)).symm

    have avoid_up : ∀ v : Plane, v 0 = 0 → l 1 ≤ v 1 → v ∉ W := by
      intro v hv0 hvl hvW
      rcases eq_or_lt_of_le hvl with h | h
      · have hveq : v = l := by ext i; fin_cases i <;> simp [hv0, hl0, h]
        exact hWsub hvW (by rw [hveq]; exact hlr)
      · have h1 := hRayNPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayN from ⟨hv0, h⟩) hRayNc
        exact axis_ray_up_unbounded (l 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_down : ∀ v : Plane, v 0 = 0 → v 1 ≤ q 1 → v ∉ W := by
      intro v hv0 hvq hvW
      rcases eq_or_lt_of_le hvq with h | h
      · have hveq : v = q := by ext i; fin_cases i <;> simp [hv0, hq0, h]
        exact hWsub hvW (by rw [hveq]; exact hqr)
      · have h1 := hRaySPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayS from ⟨hv0, h⟩) hRaySc
        exact axis_ray_down_unbounded (q 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_mid : ∀ v : Plane, v 0 = 0 → p 1 ≤ v 1 → v 1 ≤ m 1 → v ∉ W := by
      intro v hv0 hvp hvm hvW
      rcases eq_or_lt_of_le hvp with h | h
      · have hveq : v = p := by ext i; fin_cases i <;> simp [hv0, hp0, h]
        exact hWsub hvW (by rw [hveq]; exact hpr)
      · rcases eq_or_lt_of_le hvm with h' | h'
        · have hveq : v = m := by ext i; fin_cases i <;> simp [hv0, hm0, h']
          exact hWsub hvW (by rw [hveq]; exact hmr)
        · exact (Set.disjoint_left.mp hWU_disj hvW) (hMidU ⟨hv0, ⟨h, h'⟩⟩)

    have hWE : W ⊆ E := by
      intro v hvW
      by_contra hvE
      rw [hEdef, Set.mem_setOf_eq] at hvE
      have hvEc : v ∈ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := hvE
      have hEcc : {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} ⊆ (range r)ᶜ :=
        fun u hu hur => hu (hErect hur)
      have h1 := isPreconnected_rect_compl.subset_connectedComponentIn hvEc hEcc
      have hup : {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi (2:ℝ)}
          ⊆ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := by
        rintro u ⟨_, hu1⟩ ⟨_, hu2⟩
        rw [mem_Icc] at hu2; rw [mem_Ioi] at hu1; linarith [hu2.2]
      exact axis_ray_up_unbounded 2 (hwb.subset (subset_trans hup (compW hvW ▸ h1)))

    have hnl_cont : ContinuousOn (segP (!₂[(0:ℝ), 2]) l) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨lm, hlm_cont, hlm_a, hlm_b, hlm_mem⟩ :=
      arc_path (hpcJn.joinedIn l ⟨hlJn, hlab⟩ m ⟨hmJn, hmab⟩)
    have hmp_cont : ContinuousOn (segP m p) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨pq, hpq_cont, hpq_a, hpq_b, hpq_mem⟩ :=
      arc_path (hpcJs.joinedIn p ⟨hpJs, hpab⟩ q ⟨hqJs, hqab⟩)
    have hqs_cont : ContinuousOn (segP q (!₂[(0:ℝ), -2])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨β, hβcont, hβa, hβb, hβmem⟩ :=
      concatPath5 hnl_cont hlm_cont hmp_cont hpq_cont hqs_cont
        (by rw [segP_one, hlm_a]) (by rw [hlm_b, segP_neg1]) (by rw [segP_one, hpq_a])
        (by rw [hpq_b, segP_neg1])
    have hβE : ∀ t ∈ Icc (-1:ℝ) 1, β t 0 ∈ Icc (-1:ℝ) 1 ∧ β t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hn0]; exact hIcc0x) (by rw [hl0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 (by rw [hn1]; exact hIcc2y) hlE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hm0]; exact hIcc0x) (by rw [hp0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hmE1 hpE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hq0]; exact hIcc0x) (by rw [hs0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hqE1 (by rw [hs1]; exact hIccm2y) hu⟩
    have hβmiss : ∀ t ∈ Icc (-1:ℝ) 1, β t ∉ W := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_up _ ?_ ?_
        · rw [segP_coord, hn0, hl0]; ring
        · rw [segP_coord, hn1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hlE1.2]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_mid _ ?_ ?_ ?_
        · rw [segP_coord, hm0, hp0]; ring
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_down _ ?_ ?_
        · rw [segP_coord, hq0, hs0]; ring
        · rw [segP_coord, hs1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hqE1.1]

    have hfrW : frontier W = range r := by
      have hexists : ∃ y ∈ (range r)ᶜ,
          connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ w := by
        refine ⟨z₀, hz₀c, ?_⟩
        rw [← hUdef, ← hWdef]; exact fun h => hWne h.symm
      have hcbe := component_boundary_eq hbr hcont hinj hw hexists
      rwa [← hWdef] at hcbe
    have hafrW : (!₂[(-1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hm
    have hbfrW : (!₂[(1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hp
    have haclW : (!₂[(-1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hafrW
    have hbclW : (!₂[(1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hbfrW

    set βimg : Set Plane := β '' Icc (-1:ℝ) 1 with hβimgdef
    have hβimg_closed : IsClosed βimg := (isCompact_Icc.image_of_continuousOn hβcont).isClosed
    have ha_notβ : (!₂[(-1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, hta⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hn0, hl0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hm0, hp0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hq0, hs0]; ring
        rw [ha0] at hcz; norm_num at hcz
    have hb_notβ : (!₂[(1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, htb⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hn0, hl0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hm0, hp0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hq0, hs0]; ring
        rw [hb0] at hcz; norm_num at hcz
    obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ ha_notβ
    obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ hb_notβ

    rw [Metric.mem_closure_iff] at haclW hbclW
    obtain ⟨a₁, ha₁W, ha₁d⟩ := haclW εa hεa
    obtain ⟨b₁, hb₁W, hb₁d⟩ := hbclW εb hεb
    have ha₁E : a₁ 0 ∈ Icc (-1:ℝ) 1 ∧ a₁ 1 ∈ Icc (-2:ℝ) 2 := hWE ha₁W
    have hb₁E : b₁ 0 ∈ Icc (-1:ℝ) 1 ∧ b₁ 1 ∈ Icc (-2:ℝ) 2 := hWE hb₁W

    have hHp1_cont : ContinuousOn (segP (!₂[(-1:ℝ), 0]) a₁) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨Harc, hHarc_cont, hHarc_a, hHarc_b, hHarc_mem⟩ :=
      arc_path (hWpc.joinedIn a₁ ha₁W b₁ hb₁W)
    have hHp3_cont : ContinuousOn (segP b₁ (!₂[(1:ℝ), 0])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨H, hHcont, hHa, hHb, hHmem⟩ :=
      concatPath3 hHp1_cont hHarc_cont hHp3_cont
        (by rw [segP_one, hHarc_a]) (by rw [hHarc_b, segP_neg1])
    have hHa0 : H (-1) 0 = -1 := by rw [hHa, segP_neg1, ha0]
    have hHb0 : H 1 0 = 1 := by rw [hHb, segP_one, hb0]
    have hHE : ∀ t ∈ Icc (-1:ℝ) 1, H t 0 ∈ Icc (-1:ℝ) 1 ∧ H t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [ha0]; exact hIccm1x) ha₁E.1 hu,
          segP_coord_mem_Icc 1 (by rw [ha1]; exact hIcc0y) ha₁E.2 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hWE (hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 hb₁E.1 (by rw [hb0]; exact hIcc1x) hu,
          segP_coord_mem_Icc 1 hb₁E.2 (by rw [hb1]; exact hIcc0y) hu⟩
    have hHmiss : ∀ t ∈ Icc (-1:ℝ) 1, H t ∉ βimg := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP (!₂[(-1:ℝ), 0]) a₁ u ∈ Metric.ball (!₂[(-1:ℝ), 0] : Plane) εa := by
          rw [Metric.mem_ball]
          calc dist (segP (!₂[(-1:ℝ), 0]) a₁ u) (!₂[(-1:ℝ), 0])
                ≤ dist a₁ (!₂[(-1:ℝ), 0]) := segP_dist_le _ _ hu
            _ < εa := by rw [dist_comm]; exact ha₁d
        exact hballa hin hmemβ
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        obtain ⟨t', ht', ht'e⟩ := hmemβ
        exact hβmiss t' ht' (by rw [ht'e]; exact hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP b₁ (!₂[(1:ℝ), 0]) u ∈ Metric.ball (!₂[(1:ℝ), 0] : Plane) εb := by
          rw [Metric.mem_ball]
          calc dist (segP b₁ (!₂[(1:ℝ), 0]) u) (!₂[(1:ℝ), 0])
                ≤ dist b₁ (!₂[(1:ℝ), 0]) := segP_dist_le' _ _ hu
            _ < εb := by rw [dist_comm]; exact hb₁d
        exact hballb hin hmemβ

    set v : ℝ → Plane := fun t => β (-t) with hvdef
    have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) :=
      hβcont.comp continuous_neg.continuousOn (fun t ht => by
        rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht; rw [mem_Icc] at ht
      exact hβE (-t) (by rw [mem_Icc]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hv1 : v (-1) 1 = -2 := by show β (-(-1)) 1 = -2; rw [neg_neg, hβb, segP_one, hs1]
    have hv2 : v 1 1 = 2 := by show β (-1) 1 = 2; rw [hβa, segP_neg1, hn1]
    obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1) (by norm_num : (-2:ℝ) ≤ 2)
      H v hHcont hvcont hHE hvE hHa0 hHb0 hv1 hv2
    apply hHmiss s hs
    rw [heq]
    exact Set.mem_image_of_mem β (show (-t) ∈ Icc (-1:ℝ) 1 by
      rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)

  intro x hx y hy hxb hyb
  rw [KEY x hx hxb, KEY y hy hyb]

theorem step_B_bounded_unique (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  intro x hx y hy hxb hyb
  obtain ⟨a, ha, b, hb, hfar0, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0:ℝ) < 2 / dist a b := by positivity
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  have hrc : (range r')ᶜ = (T : Plane → Plane) '' (range r)ᶜ := by rw [hrange, himg]
  have hm' : (!₂[(-1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b :=
          mul_le_mul_of_nonneg_left (hfar0 z hz w hw) hcpos.le
      _ = 2 := by field_simp

  have hTx : T x ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hx
  have hTy : T y ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hy
  have hccx : connectedComponentIn (range r')ᶜ (T x)
      = T '' connectedComponentIn (range r)ᶜ x := by
    rw [hrc]; exact (T.image_connectedComponentIn hx).symm
  have hccy : connectedComponentIn (range r')ᶜ (T y)
      = T '' connectedComponentIn (range r)ᶜ y := by
    rw [hrc]; exact (T.image_connectedComponentIn hy).symm
  have hTxb : IsBounded (connectedComponentIn (range r')ᶜ (T x)) := by
    rw [hccx]; exact (isBounded_image_scaling hcpos hscale _).mpr hxb
  have hTyb : IsBounded (connectedComponentIn (range r')ᶜ (T y)) := by
    rw [hccy]; exact (isBounded_image_scaling hcpos hscale _).mpr hyb
  have hEq := step_B_normalized hbr hr'cont hr'inj hm' hp' hfar'
    (T x) hTx (T y) hTy hTxb hTyb
  rw [hccx, hccy] at hEq
  exact Set.image_injective.mpr T.injective hEq

theorem jordan_curve_of_brouwer (hbr : BrouwerFPT)
    (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 := by

  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  set a : ↥((range r)ᶜ) := ⟨x₀, hx₀S⟩ with ha
  set b : ↥((range r)ᶜ) := ⟨x₁, hx₁S⟩ with hb

  have hne : connectedComponentIn (range r)ᶜ x₀ ≠ connectedComponentIn (range r)ᶜ x₁ := by
    intro heq
    exact hx₀u (heq ▸ hx₁b)
  have hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b :=
    (Counting.connectedComponents_subtype_eq_iff hx₀S hx₁S).not.mpr hne

  have hcover : ∀ z : ↥((range r)ᶜ),
      ConnectedComponents.mk z = ConnectedComponents.mk a
        ∨ ConnectedComponents.mk z = ConnectedComponents.mk b := by
    intro z
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z.val)
    · right
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₁S).mpr
        (step_B_bounded_unique hbr hcont hinj z.val z.2 x₁ hx₁S hzb hx₁b)
    · left
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₀S).mpr
        (unbounded_component_unique r hcont hzb hx₀u)
  exact Counting.nat_card_connectedComponents_eq_two a b hab hcover

theorem jordan_curve
    (r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 := by

  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  exact jordan_curve_of_brouwer hbr r _hcont _hinj

end Poincare.Topology.Plane.Jordan
