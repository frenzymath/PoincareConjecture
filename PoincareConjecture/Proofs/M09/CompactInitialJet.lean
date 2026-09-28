import PoincareConjecture.Proofs.M09.SpatialDifferentialJet
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M09

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_initialSlice_fderiv_bound (f : E × ℝ → V) (U : Set (E × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hzeroU : ∀ x, (x, (0 : ℝ)) ∈ U) (q : V) (hzero : ∀ x, f (x, 0) = q)
    (L : E →L[ℝ] V) (hjet : ∀ x, HasDerivAt (fun t ↦ f (x, t)) (L x) 0)
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ s, 0 ≤ s → s < δ →
      (x, s) ∈ U ∧ ‖fderiv ℝ (fun y ↦ f (y, s)) x - s • L‖ ≤ ε * s := by
  let B : E × ℝ → E →L[ℝ] V := fun z ↦ fderiv ℝ (fun y ↦ f (y, z.2)) z.1
  let C : E × ℝ → E →L[ℝ] V := fun z ↦ deriv (fun t ↦ B (z.1, t)) z.2
  have hB : ContDiffOn ℝ ∞ B U := contDiffOn_initialSlice_fderiv f U hU hf
  have hC : ContDiffOn ℝ ∞ C U := contDiffOn_timeSlice_deriv B U hU hB
  have hBzero (x : E) : B (x, 0) = 0 := initialSlice_fderiv_zero f q hzero x
  have hCzero (x : E) : C (x, 0) = L :=
    (hasDerivAt_initialSlice_fderiv_zero f U hU hf hzeroU L hjet x).deriv
  let W := U ∩ C ⁻¹' Metric.ball L ε
  have hW : IsOpen W := hC.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hKW : K ×ˢ {(0 : ℝ)} ⊆ W := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hzeroU x, ?_⟩
    simpa only [Set.mem_preimage, hCzero, Metric.mem_ball, dist_self] using hε
  obtain ⟨N, V0, _, hV0, hKN, hzeroV, hNV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hW hKW
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp
    (hV0.mem_nhds (hzeroV (Set.mem_singleton 0)))
  have hnear (x : E) (hx : x ∈ K) (r : ℝ) (hr : 0 ≤ r) (hrδ : r < δ) :
      (x, r) ∈ W := by
    apply hNV
    refine ⟨hKN hx, hδV ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hr] using hrδ
  refine ⟨δ, hδ, ?_⟩
  intro x hx s hs hsδ
  refine ⟨(hnear x hx s hs hsδ).1, ?_⟩
  let H : ℝ → E →L[ℝ] V := fun r ↦ B (x, r) - r • L
  have hD (r : ℝ) (hr : r ∈ Set.Icc 0 s) : HasDerivAt H (C (x, r) - L) r := by
    have hb : DifferentiableAt ℝ (fun t ↦ B (x, t)) r :=
      ((hB.contDiffAt (hU.mem_nhds (hnear x hx r hr.1 (hr.2.trans_lt hsδ)).1)).comp r
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    convert! hb.hasDerivAt.sub ((hasDerivAt_id r).smul_const L) using 1 <;>
      simp only [H, C, Pi.sub_apply, id_eq, one_smul]
  have hbound (r : ℝ) (hr : r ∈ Set.Ico 0 s) : ‖C (x, r) - L‖ ≤ ε := by
    have h := (hnear x hx r hr.1 (hr.2.trans hsδ)).2
    exact (show ‖C (x, r) - L‖ < ε by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using h).le
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun r hr ↦ (hD r hr).hasDerivWithinAt) hbound s ⟨hs, le_rfl⟩
  simpa only [H, hBzero, zero_smul, sub_self, sub_zero] using hm

end PoincareConjecture.Proofs.M09
