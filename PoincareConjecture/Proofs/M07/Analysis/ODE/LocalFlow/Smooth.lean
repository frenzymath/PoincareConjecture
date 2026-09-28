










import PoincareConjecture.Proofs.M07.Analysis.ODE.LocalFlow.Existence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









noncomputable section

namespace Poincare.ODE.LocalFlow

open Set Metric Filter
open scoped ContDiff Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_cutoff_smul
    {U : Set E} (hU : IsOpen U) {χ : E → ℝ} {F : E → E}
    (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) :
    ContDiff ℝ ∞ (fun x => χ x • F x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds (hχU hx)))
  · have heq : (fun y => χ y • F y) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

variable [FiniteDimensional ℝ E]




theorem exists_smooth_localFlow
    {U : Set E} (hU : IsOpen U) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ (V : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ x ∈ V, Φ (x, 0) = x) ∧
      (∀ x ∈ V, ∀ t ∈ Ioo (-δ) δ, Φ (x, t) ∈ U) ∧
      (∀ x ∈ V, ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt (fun s => Φ (x, s)) (F (Φ (x, t))) t) := by
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx₀)
  let χ : ContDiffBump x₀ :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  let G : E → E := fun x => χ x • F x
  have hχU : tsupport (χ : E → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact hdU
  have hG : ContDiff ℝ ∞ G := contDiff_cutoff_smul hU χ.contDiff hχU hF
  have hGF : EqOn G F (ball x₀ (d / 2)) := by
    intro x hx
    change χ x • F x = F x
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]
  obtain ⟨r, ε, hr, hε, Φ, hΦ, ρ, T, hρ, hT, hρr, hTε, hSmooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := fun _ => G) (t₀ := 0) (x₀ := x₀)
      (hG.comp contDiff_snd)
  simp only [zero_sub, zero_add] at hΦ hSmooth
  let D : Set (E × ℝ) := ball x₀ ρ ×ˢ Ioo (-T) T
  let W : Set (E × ℝ) := D ∩ Φ ⁻¹' ball x₀ (d / 2)
  have hWopen : IsOpen W :=
    hSmooth.continuousOn.isOpen_inter_preimage (isOpen_ball.prod isOpen_Ioo) isOpen_ball
  have hWmem : (x₀, 0) ∈ W := by
    refine ⟨⟨mem_ball_self hρ, ⟨by linarith, hT⟩⟩, ?_⟩
    change Φ (x₀, 0) ∈ ball x₀ (d / 2)
    rw [hΦ.apply_initial x₀ (mem_closedBall_self (le_of_lt hr))]
    exact mem_ball_self (half_pos hd)
  obtain ⟨a, ha, haW⟩ := Metric.isOpen_iff.mp hWopen (x₀, 0) hWmem
  have hsub : ball x₀ a ×ˢ Ioo (-a) a ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    apply haW
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right]
    exact ⟨hx, abs_lt.mpr ht⟩
  have hinit : ∀ x ∈ ball x₀ a, Φ (x, 0) = x := by
    intro x hx
    have hxρ := (hsub (show (x, 0) ∈ _ from ⟨hx, ⟨by linarith, ha⟩⟩)).1.1
    exact hΦ.apply_initial x (ball_subset_closedBall (ball_subset_ball hρr hxρ))
  have hmaps : ∀ x ∈ ball x₀ a, ∀ t ∈ Ioo (-a) a, Φ (x, t) ∈ U := by
    intro x hx t ht
    exact hdU (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall (hsub (show (x, t) ∈ _ from ⟨hx, ht⟩)).2))
  refine ⟨ball x₀ a, a, Φ, isOpen_ball, mem_ball_self ha, ?_, ha,
    hSmooth.mono (fun q hq => (hsub hq).1), hinit, hmaps, ?_⟩
  · intro x hx
    simpa only [hinit x hx] using hmaps x hx 0 ⟨by linarith, ha⟩
  · intro x hx t ht
    have hq := hsub (show (x, t) ∈ _ from ⟨hx, ht⟩)
    have htε : t ∈ Ioo (-ε) ε :=
      ⟨lt_of_le_of_lt (neg_le_neg hTε) hq.1.2.1, hq.1.2.2.trans_le hTε⟩
    have hderiv := hΦ.hasDerivWithinAt x
      (ball_subset_closedBall (ball_subset_ball hρr hq.1.1)) t
      (Ioo_subset_Icc_self htε)
    have hderiv' := hderiv.hasDerivAt (Icc_mem_nhds htε.1 htε.2)
    rw [show G (Φ (x, t)) = F (Φ (x, t)) from hGF hq.2] at hderiv'
    exact hderiv'

end Poincare.ODE.LocalFlow
