









import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.Variational


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace Poincare.ODE.LocalFlow

section VariationalSolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

attribute [local instance] parametricLinearODEEndoNormedAddCommGroup
attribute [local instance] parametricLinearODEEndoNormedSpace
attribute [local instance] parametricLinearODEDerivativeNormedAddCommGroup
attribute [local instance] parametricLinearODEDerivativeNormedSpace

omit [NormedSpace ℝ F] in
theorem linearODESolution_dist_le
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    {x₁ x₂ : F} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U)
    {α β : ℝ} (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    {K η : ℝ} (hK_nn : 0 ≤ K)
    (hA₁_bd : ∀ s ∈ Set.Icc α β, ‖A x₁ s‖ ≤ K)
    (hdiff_bd : ∀ s ∈ Set.Icc α β,
      ‖(A x₂ s - A x₁ s) (linearODESolution A a b' h₀ Z₀ x₂ s)‖ ≤ η)
    {t : ℝ} (ht : t ∈ Set.Icc α β) :
    ‖linearODESolution A a b' h₀ Z₀ x₁ t - linearODESolution A a b' h₀ Z₀ x₂ t‖
      ≤ gronwallBound ‖Z₀ x₁ - Z₀ x₂‖ K η |t - h₀| := by
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hZ_deriv₁ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
    fun s hs => linearODESolution_hasDerivAt h₀_mem hA_cont hx₁ hs
  have hZ_deriv₂ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
    fun s hs => linearODESolution_hasDerivAt h₀_mem hA_cont hx₂ hs
  have hZ_init₁ : Z x₁ h₀ = Z₀ x₁ := linearODESolution_init A a b' h₀ Z₀ x₁
  have hZ_init₂ : Z x₂ h₀ = Z₀ x₂ := linearODESolution_init A a b' h₀ Z₀ x₂
  have hIcc_sub_Ioo : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hZ_cont₁ : ContinuousOn (Z x₁) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₁ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hZ_cont₂ : ContinuousOn (Z x₂) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₂ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hα_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hh₀_le_β : h₀ ≤ β := hh₀_mem.2
  rcases le_total h₀ t with hht | hth
  · have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
      ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
    have hZ₁_cont_fwd : ContinuousOn (Z x₁) (Set.Icc h₀ β) := hZ_cont₁.mono hIcc_fwd_sub
    have hZ₂_cont_fwd : ContinuousOn (Z x₂) (Set.Icc h₀ β) := hZ_cont₂.mono hIcc_fwd_sub
    have hZ₁_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hZ₂_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hA₁_bd_fwd : ∀ s ∈ Set.Icc h₀ β, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_fwd_sub hs)
    have hdiff_bd_fwd : ∀ s ∈ Set.Icc h₀ β,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_fwd_sub hs)
    have hres := linearODE_gronwall_forward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (h₀ := h₀) (β := β) (K := K) (η := η)
      hK_nn hZ₁_cont_fwd hZ₂_cont_fwd hZ₁_deriv_fwd hZ₂_deriv_fwd
      hA₁_bd_fwd hdiff_bd_fwd t ⟨hht, ht.2⟩
    have h_init_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_init₁, hZ_init₂]
    rw [h_init_eq] at hres
    have h_abs : |t - h₀| = t - h₀ := abs_of_nonneg (by linarith)
    rw [h_abs]
    exact hres
  · have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
      ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
    have hZ₁_cont_bwd : ContinuousOn (Z x₁) (Set.Icc α h₀) := hZ_cont₁.mono hIcc_bwd_sub
    have hZ₂_cont_bwd : ContinuousOn (Z x₂) (Set.Icc α h₀) := hZ_cont₂.mono hIcc_bwd_sub
    have hZ₁_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hZ₂_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hA₁_bd_bwd : ∀ s ∈ Set.Icc α h₀, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_bwd_sub hs)
    have hdiff_bd_bwd : ∀ s ∈ Set.Icc α h₀,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_bwd_sub hs)
    have hres := linearODE_gronwall_backward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (α := α) (h₀ := h₀) (K := K) (η := η)
      hα_le_h₀ hK_nn hZ₁_cont_bwd hZ₂_cont_bwd hZ₁_deriv_bwd hZ₂_deriv_bwd
      hA₁_bd_bwd hdiff_bd_bwd t ⟨ht.1, hth⟩
    have h_init_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_init₁, hZ_init₂]
    rw [h_init_eq] at hres
    have h_abs : |t - h₀| = h₀ - t := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h_abs]
    exact hres

omit [CompleteSpace G] in
theorem norm_le_gronwallBound_on_Icc
    {R R' : ℝ → G} {α β h₀ t r₀ K η : ℝ}
    (hh₀_mem : h₀ ∈ Set.Icc α β) (ht_mem : t ∈ Set.Icc α β)
    (hr₀_nn : 0 ≤ r₀) (hK_nn : 0 ≤ K) (hη_nn : 0 ≤ η)
    (hR_cont : ContinuousOn R (Set.Icc α β))
    (hR_deriv : ∀ s ∈ Set.Icc α β, HasDerivAt R (R' s) s)
    (hR_init : ‖R h₀‖ ≤ r₀)
    (hR_bd : ∀ s ∈ Set.Icc α β, ‖R' s‖ ≤ K * ‖R s‖ + η) :
    ‖R t‖ ≤ gronwallBound r₀ K η (β - α) := by
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem.2
  rcases le_total h₀ t with hht | hth
  · have ht_fwd : t ∈ Set.Icc h₀ β := ⟨hht, ht_mem.2⟩
    have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
      ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
    have hR_cont_fwd : ContinuousOn R (Set.Icc h₀ β) :=
      hR_cont.mono hIcc_fwd_sub
    have hR_deriv_within_right : ∀ s ∈ Set.Ico h₀ β,
        HasDerivWithinAt R (R' s) (Set.Ici s) s := fun s hs =>
      (hR_deriv s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have h_bound_fwd : ∀ s ∈ Set.Ico h₀ β,
        ‖R' s‖ ≤ K * ‖R s‖ + η := fun s hs =>
      hR_bd s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
      hR_cont_fwd hR_deriv_within_right hR_init h_bound_fwd t ht_fwd
    have h_t_sub_le : t - h₀ ≤ β - α := by
      linarith [ht_mem.2, h_α_le_h₀]
    have h_mono :
        gronwallBound r₀ K η (t - h₀) ≤
          gronwallBound r₀ K η (β - α) :=
      gronwallBound_mono hr₀_nn hη_nn hK_nn h_t_sub_le
    exact hgw.trans h_mono
  · have ht_bwd : t ∈ Set.Icc α h₀ := ⟨ht_mem.1, hth⟩
    have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
      ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
    let Rb : ℝ → G := fun s => R (2 * h₀ - s)
    have h_h₀_le_2h₀_t : h₀ ≤ 2 * h₀ - t := by linarith
    have h_dom_swap :
        ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
      intro s hs
      refine ⟨?_, ?_⟩ <;> linarith [hs.1, hs.2, ht_bwd.1]
    have hRb_cont : ContinuousOn Rb (Set.Icc h₀ (2 * h₀ - t)) := by
      apply ContinuousOn.comp (hR_cont.mono hIcc_bwd_sub)
        (s := Set.Icc h₀ (2 * h₀ - t)) (t := Set.Icc α h₀)
        (f := fun s => 2 * h₀ - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_swap
    have hRb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        HasDerivAt Rb (-(R' (2 * h₀ - s))) s := by
      intro s hs
      have hd := hR_deriv (2 * h₀ - s)
        (hIcc_bwd_sub (h_dom_swap s hs))
      have hchain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
        refine (((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)).congr_of_eventuallyEq
          ?_).congr_deriv ?_
        · exact Filter.Eventually.of_forall fun r => by
            change 2 * h₀ - r = 2 * h₀ - r
            rfl
        · norm_num
      have hd' := hd.scomp s hchain
      rw [show ((-1 : ℝ) • R' (2 * h₀ - s) : G) =
        -(R' (2 * h₀ - s)) by exact neg_one_smul ℝ _] at hd'
      exact hd'
    have hRb_deriv_within_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        HasDerivWithinAt Rb (-(R' (2 * h₀ - s))) (Set.Ici s) s :=
      fun s hs => (hRb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hRb_init : Rb h₀ = R h₀ := by
      change R (2 * h₀ - h₀) = R h₀
      congr 1
      ring
    have hRb_init_bd : ‖Rb h₀‖ ≤ r₀ := by
      rw [hRb_init]
      exact hR_init
    have hRb_bd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        ‖-(R' (2 * h₀ - s))‖ ≤ K * ‖Rb s‖ + η := by
      intro s hs
      have hin : 2 * h₀ - s ∈ Set.Icc α β :=
        hIcc_bwd_sub (h_dom_swap s (Set.Ico_subset_Icc_self hs))
      have hbound := hR_bd (2 * h₀ - s) hin
      rw [norm_neg]
      exact hbound
    have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
      hRb_cont hRb_deriv_within_right hRb_init_bd hRb_bd (2 * h₀ - t)
      (right_mem_Icc.mpr h_h₀_le_2h₀_t)
    have hRb_t : Rb (2 * h₀ - t) = R t := by
      change R (2 * h₀ - (2 * h₀ - t)) = R t
      congr 1
      ring
    rw [hRb_t] at hgw_bwd
    have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
    rw [h_time] at hgw_bwd
    have h_h₀_sub_t_le : h₀ - t ≤ β - α := by
      linarith [ht_bwd.1, h_h₀_le_β]
    have h_mono :
        gronwallBound r₀ K η (h₀ - t) ≤
          gronwallBound r₀ K η (β - α) :=
      gronwallBound_mono hr₀_nn hη_nn hK_nn h_h₀_sub_t_le
    exact hgw_bwd.trans h_mono

theorem linearODESolution_local_lipschitz_on_Icc
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    {x : F} {α β δ M P Q L : ℝ}
    (hx : x ∈ U)
    (ha_lt_α : a < α) (hβ_lt_b' : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    (hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b')
    (hclosedBall_sub : Metric.closedBall x δ ⊆ U)
    (hδ_nn : 0 ≤ δ) (hM_nn : 0 ≤ M) (hP_nn : 0 ≤ P)
    (hQ_nn : 0 ≤ Q) (hL_nn : 0 ≤ L)
    (hAx_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M)
    (hDA_bd : ∀ y ∈ Metric.closedBall x δ, ∀ s ∈ Set.Icc α β,
      ‖fderiv ℝ (fun z => A z s) y‖ ≤ P)
    (hZ_bd : ∀ y ∈ Metric.closedBall x δ, ∀ s ∈ Set.Icc α β,
      ‖linearODESolution A a b' h₀ Z₀ y s‖ ≤ Q)
    (hDZ₀_bd : ∀ y ∈ Metric.closedBall x δ, ‖fderiv ℝ Z₀ y‖ ≤ L)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) :
    ∀ h : F, ‖h‖ ≤ δ → ∀ s ∈ Set.Icc α β,
      ‖linearODESolution A a b' h₀ Z₀ (x + h) s -
          linearODESolution A a b' h₀ Z₀ x s‖ ≤
        gronwallBound L M (P * Q) (β - α) * ‖h‖ := by
  intro h hh_bd s hs
  have hdist_xh_x : dist (x + h) x = ‖h‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hxh_ball : x + h ∈ Metric.closedBall x δ := by
    rw [Metric.mem_closedBall, hdist_xh_x]
    exact hh_bd
  have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
  have hConv : Convex ℝ (Metric.closedBall x δ) := convex_closedBall _ _
  have hZ₀_lip : ‖Z₀ (x + h) - Z₀ x‖ ≤ L * ‖h‖ := by
    have hdiff : ∀ y ∈ Metric.closedBall x δ, DifferentiableAt ℝ Z₀ y :=
      fun y hy => (hZ₀_diff y (hclosedBall_sub hy)).differentiableAt
    have hres := hConv.norm_image_sub_le_of_norm_fderiv_le
      hdiff hDZ₀_bd (Metric.mem_closedBall_self hδ_nn) hxh_ball
    have hsub_eq : x + h - x = h := by abel
    rw [hsub_eq] at hres
    exact hres
  have h_force : ∀ s' ∈ Set.Icc α β,
      ‖(A (x + h) s' - A x s')
          (linearODESolution A a b' h₀ Z₀ (x + h) s')‖ ≤
        (P * Q) * ‖h‖ := by
    intro s' hs'
    have hZxh_bd :
        ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ ≤ Q :=
      hZ_bd (x + h) hxh_ball s' hs'
    have hAdiff_bd : ‖A (x + h) s' - A x s'‖ ≤ P * ‖h‖ := by
      have hbd : ∀ y ∈ Metric.closedBall x δ,
          ‖fderiv ℝ (fun z => A z s') y‖ ≤ P :=
        fun y hy => hDA_bd y hy s' hs'
      have hdiff : ∀ y ∈ Metric.closedBall x δ,
          DifferentiableAt ℝ (fun z => A z s') y := fun y hy =>
        (hA_diff y (hclosedBall_sub hy) s' (hIcc_sub hs')).differentiableAt
      have hres := hConv.norm_image_sub_le_of_norm_fderiv_le
        hdiff hbd (Metric.mem_closedBall_self hδ_nn) hxh_ball
      have hsub_eq : x + h - x = h := by abel
      rw [hsub_eq] at hres
      exact hres
    have h1 :
        ‖(A (x + h) s' - A x s')
            (linearODESolution A a b' h₀ Z₀ (x + h) s')‖ ≤
          ‖A (x + h) s' - A x s'‖ *
            ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ :=
      (A (x + h) s' - A x s').le_opNorm _
    have h2 :
        ‖A (x + h) s' - A x s'‖ *
            ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ ≤
          (P * ‖h‖) * Q :=
      mul_le_mul hAdiff_bd hZxh_bd (norm_nonneg _)
        (mul_nonneg hP_nn (norm_nonneg _))
    calc
      ‖(A (x + h) s' - A x s')
          (linearODESolution A a b' h₀ Z₀ (x + h) s')‖
          ≤ ‖A (x + h) s' - A x s'‖ *
              ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ := h1
      _ ≤ (P * ‖h‖) * Q := h2
      _ = P * Q * ‖h‖ := by ring
  have hgw := linearODESolution_dist_le (A := A) (Z₀ := Z₀)
    h₀_mem hA_cont hx hxh_U ha_lt_α hβ_lt_b' hh₀_mem
    hM_nn hAx_bd h_force hs
  have h_init_bd : ‖Z₀ x - Z₀ (x + h)‖ ≤ L * ‖h‖ := by
    rw [show Z₀ x - Z₀ (x + h) = -(Z₀ (x + h) - Z₀ x) by abel, norm_neg]
    exact hZ₀_lip
  have h_abs_le : |s - h₀| ≤ β - α := by
    rcases le_total h₀ s with hle | hle
    · rw [abs_of_nonneg (by linarith)]
      linarith [hh₀_mem.1, hs.2]
    · rw [abs_of_nonpos (by linarith)]
      linarith [hs.1, hh₀_mem.2]
  rw [show linearODESolution A a b' h₀ Z₀ x s -
      linearODESolution A a b' h₀ Z₀ (x + h) s =
      -(linearODESolution A a b' h₀ Z₀ (x + h) s -
        linearODESolution A a b' h₀ Z₀ x s) by abel, norm_neg] at hgw
  have h_gb_mono_δ :
      gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M (P * Q * ‖h‖) |s - h₀| ≤
        gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := by
    by_cases hMeq : M = 0
    · simp only [gronwallBound_K0, hMeq]
      linarith
    · simp only [gronwallBound_of_K_ne_0 hMeq]
      have hexp_nn : 0 ≤ Real.exp (M * |s - h₀|) := (Real.exp_pos _).le
      have hmul : ‖Z₀ x - Z₀ (x + h)‖ * Real.exp (M * |s - h₀|) ≤
          (L * ‖h‖) * Real.exp (M * |s - h₀|) :=
        mul_le_mul_of_nonneg_right h_init_bd hexp_nn
      linarith
  have h_gb_mono_x :
      gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| ≤
        gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) :=
    gronwallBound_mono (mul_nonneg hL_nn (norm_nonneg _))
      (mul_nonneg (mul_nonneg hP_nn hQ_nn) (norm_nonneg _))
      hM_nn h_abs_le
  have h_gb_scale :
      gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) =
        ‖h‖ * gronwallBound L M (P * Q) (β - α) := by
    by_cases hMeq : M = 0
    · rw [hMeq]
      simp only [gronwallBound_K0]
      ring
    · simp only [gronwallBound_of_K_ne_0 hMeq]
      field_simp
  calc
    ‖linearODESolution A a b' h₀ Z₀ (x + h) s -
        linearODESolution A a b' h₀ Z₀ x s‖
        ≤ gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M
            (P * Q * ‖h‖) |s - h₀| := hgw
    _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := h_gb_mono_δ
    _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) := h_gb_mono_x
    _ = ‖h‖ * gronwallBound L M (P * Q) (β - α) := h_gb_scale
    _ = gronwallBound L M (P * Q) (β - α) * ‖h‖ := mul_comm _ _

theorem linearODESolution_hasFDerivAt_param
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasFDerivAt (fun y => linearODESolution A a b' h₀ Z₀ y t)
      (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) x := by
  classical
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  set α := (a + min t h₀) / 2 with hα_def
  set β := (b' + max t h₀) / 2 with hβ_def
  have hmin_lt_a : a < min t h₀ := lt_min ht.1 h₀_mem.1
  have hmax_lt_b' : max t h₀ < b' := max_lt ht.2 h₀_mem.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_h₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have hh₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
  have ha_lt_α : a < α := by rw [hα_def]; linarith
  have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
  have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
  have hα_le_β : α ≤ β := by linarith
  have hh₀_mem_Icc : h₀ ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_h₀),
     le_of_lt (lt_of_le_of_lt hh₀_le_max hmax_lt_β)⟩
  have ht_mem_Icc : t ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
     le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
  have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
  have hIcc_cpt : IsCompact (Set.Icc α β) := isCompact_Icc
  have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
  obtain ⟨ε_open, hε_open_pos, hball_sub⟩ :=
    Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  set δ₀ : ℝ := ε_open / 2 with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_lt : δ₀ < ε_open := by rw [hδ₀_def]; linarith
  have hclosedBall_sub : Metric.closedBall x δ₀ ⊆ U := fun y hy =>
    hball_sub (Metric.closedBall_subset_ball hδ₀_lt hy)
  have hclosedBall_cpt : IsCompact (Metric.closedBall x δ₀) :=
    isCompact_closedBall x δ₀
  set K : Set (F × ℝ) := Metric.closedBall x δ₀ ×ˢ Set.Icc α β with hK_def
  have hK_cpt : IsCompact K := hclosedBall_cpt.prod hIcc_cpt
  have hK_sub : K ⊆ U ×ˢ Set.Ioo a b' := fun p hp =>
    ⟨hclosedBall_sub hp.1, hIcc_sub hp.2⟩
  have hx_ball : x ∈ Metric.closedBall x δ₀ := Metric.mem_closedBall_self hδ₀_pos.le
  have hK_ne : K.Nonempty :=
    ⟨(x, α), hx_ball, left_mem_Icc.mpr hα_le_β⟩
  have hA_cont_K : ContinuousOn (Function.uncurry A) K := hA_cont.mono hK_sub
  have hAnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖A p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hA_cont_K
  obtain ⟨pM, _, hM_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hAnorm_cont_K
  set M : ℝ := ‖A pM.1 pM.2‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd' : ∀ p ∈ K, ‖A p.1 p.2‖ ≤ M := fun p hp => hM_bd hp
  have hDA_cont_K : ContinuousOn
      (Function.uncurry fun y s => fderiv ℝ (fun z => A z s) y) K :=
    hDA_cont.mono hK_sub
  have hDAnorm_cont_K : ContinuousOn
      (fun p : F × ℝ => ‖fderiv ℝ (fun z => A z p.2) p.1‖) K :=
    by
      refine hDA_cont_K.norm.congr ?_
      intro p _
      rfl
  obtain ⟨pP, _, hP_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hDAnorm_cont_K
  set P : ℝ := ‖fderiv ℝ (fun z => A z pP.2) pP.1‖ with hP_def
  have hP_nn : 0 ≤ P := norm_nonneg _
  have hP_bd' : ∀ p ∈ K, ‖fderiv ℝ (fun z => A z p.2) p.1‖ ≤ P :=
    fun p hp => hP_bd hp
  have hZ_cont_K : ContinuousOn (Function.uncurry Z) K :=
    (linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont).mono hK_sub
  have hZnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖Z p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hZ_cont_K
  obtain ⟨pQ, _, hQ_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hZnorm_cont_K
  set Q : ℝ := ‖Z pQ.1 pQ.2‖ with hQ_def
  have hQ_nn : 0 ≤ Q := norm_nonneg _
  have hQ_bd' : ∀ p ∈ K, ‖Z p.1 p.2‖ ≤ Q := fun p hp => hQ_bd hp
  have hDZ₀_cont_ball : ContinuousOn (fun y => fderiv ℝ Z₀ y)
      (Metric.closedBall x δ₀) := hDZ₀_cont.mono hclosedBall_sub
  have hDZ₀norm_cont_ball : ContinuousOn (fun y => ‖fderiv ℝ Z₀ y‖)
      (Metric.closedBall x δ₀) :=
    continuous_norm.comp_continuousOn hDZ₀_cont_ball
  obtain ⟨pL, _, hL_bd⟩ := hclosedBall_cpt.exists_isMaxOn
    ⟨x, hx_ball⟩ hDZ₀norm_cont_ball
  set L : ℝ := ‖fderiv ℝ Z₀ pL‖ with hL_def
  have hL_nn : 0 ≤ L := norm_nonneg _
  have hL_bd' : ∀ y ∈ Metric.closedBall x δ₀, ‖fderiv ℝ Z₀ y‖ ≤ L :=
    fun y hy => hL_bd hy
  have hAx_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M := fun s hs =>
    hM_bd' (x, s) ⟨hx_ball, hs⟩
  have hDAx_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun z => A z s) x‖ ≤ P :=
    fun s hs => hP_bd' (x, s) ⟨hx_ball, hs⟩
  have hZx_bd : ∀ s ∈ Set.Icc α β, ‖Z x s‖ ≤ Q := fun s hs =>
    hQ_bd' (x, s) ⟨hx_ball, hs⟩
  have hZ₀x_bd : ‖fderiv ℝ Z₀ x‖ ≤ L := hL_bd' x hx_ball
  set C_stab : ℝ := gronwallBound L M (P * Q) (β - α) with hC_stab_def
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have hβα_nn : 0 ≤ β - α := by linarith
  have hC_stab_nn : 0 ≤ C_stab := by
    rw [hC_stab_def]
    have h0 : gronwallBound L M (P * Q) 0 = L := gronwallBound_x0 _ _ _
    have hmono : gronwallBound L M (P * Q) 0 ≤ gronwallBound L M (P * Q) (β - α) :=
      gronwallBound_mono hL_nn hPQ_nn hM_nn hβα_nn
    linarith
  have h_stab : ∀ h : F, ‖h‖ ≤ δ₀ → ∀ s ∈ Set.Icc α β,
      ‖Z (x + h) s - Z x s‖ ≤ C_stab * ‖h‖ := by
    simpa only [hZ_def, hC_stab_def] using
      (linearODESolution_local_lipschitz_on_Icc (A := A) (Z₀ := Z₀)
        h₀_mem hA_cont hA_diff (x := x) (α := α) (β := β)
        (δ := δ₀) (M := M) (P := P) (Q := Q) (L := L) hx
        ha_lt_α hβ_lt_b' hh₀_mem_Icc hIcc_sub hclosedBall_sub
        hδ₀_pos.le hM_nn hP_nn hQ_nn hL_nn hAx_bd
        (fun y hy s hs => hP_bd' (y, s) ⟨hy, hs⟩)
        (fun y hy s hs => by
          simpa only [hZ_def] using hQ_bd' (y, s) ⟨hy, hs⟩)
        hL_bd' hZ₀_diff)
  have hUC : UniformContinuousOn
      (fun p : F × ℝ => fderiv ℝ (fun z => A z p.2) p.1) K :=
    hK_cpt.uniformContinuousOn_of_continuous hDA_cont_K
  have h_taylor : ∀ ε > (0 : ℝ), ∃ δ_ε > (0 : ℝ), δ_ε ≤ δ₀ ∧
      ∀ h : F, ‖h‖ ≤ δ_ε → ∀ s ∈ Set.Icc α β,
        ‖A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    rw [Metric.uniformContinuousOn_iff_le] at hUC
    obtain ⟨δ', hδ'_pos, hδ'_unif⟩ := hUC ε hε
    refine ⟨min δ₀ δ', lt_min hδ₀_pos hδ'_pos, min_le_left _ _, ?_⟩
    intro h hh_bd s hs
    have hh_le_δ₀ : ‖h‖ ≤ δ₀ := le_trans hh_bd (min_le_left _ _)
    have hh_le_δ' : ‖h‖ ≤ δ' := le_trans hh_bd (min_le_right _ _)
    have hball_sub_K : ∀ y ∈ Metric.closedBall x ‖h‖, y ∈ Metric.closedBall x δ₀ :=
      fun y hy => Metric.closedBall_subset_closedBall hh_le_δ₀ hy
    have hConv_h : Convex ℝ (Metric.closedBall x ‖h‖) := convex_closedBall _ _
    have hx_in_h : x ∈ Metric.closedBall x ‖h‖ :=
      Metric.mem_closedBall_self (norm_nonneg _)
    have hxh_in_h : x + h ∈ Metric.closedBall x ‖h‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : x + h - x = h := by abel
      rw [this]
    have h_pt_bd : ∀ y ∈ Metric.closedBall x ‖h‖,
        ‖fderiv ℝ (fun z => A z s) y - fderiv ℝ (fun z => A z s) x‖ ≤ ε := by
      intro y hy
      have hy_K : (y, s) ∈ K := ⟨hball_sub_K y hy, hs⟩
      have hx_K : (x, s) ∈ K := ⟨hx_ball, hs⟩
      have hdist_le : dist (y, s) (x, s) ≤ δ' := by
        rw [Prod.dist_eq]
        have : dist s s = 0 := dist_self _
        rw [this]
        have hys_dist : dist y x ≤ ‖h‖ := hy
        exact max_le (le_trans hys_dist hh_le_δ') (le_of_lt hδ'_pos)
      have hunif := hδ'_unif (y, s) hy_K (x, s) hx_K hdist_le
      rw [dist_eq_norm] at hunif
      exact hunif
    have hHasFDeriv : ∀ y ∈ Metric.closedBall x ‖h‖,
        HasFDerivWithinAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y)
          (Metric.closedBall x ‖h‖) y := fun y hy =>
      (hA_diff y (hclosedBall_sub (hball_sub_K y hy)) s (hIcc_sub hs)).hasFDerivWithinAt
    have hres := hConv_h.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hHasFDeriv h_pt_bd hx_in_h hxh_in_h
    have hsub_eq : x + h - x = h := by abel
    rw [hsub_eq] at hres
    exact hres
  have hW_deriv : ∀ h : F, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (variationalSolution A a b' h₀ Z₀ x h ·)
        ((fderiv ℝ (fun y => A y s) x) h (Z x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x h s)) s := fun h s hs =>
    variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx h hs
  have hW_init_eq : ∀ h : F,
      variationalSolution A a b' h₀ Z₀ x h h₀ = (fderiv ℝ Z₀ x) h := fun h =>
    variationalW_init A a b' h₀ Z₀ x h
  have hZ_deriv : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (Z y ·) (A y s (Z y s)) s := fun y hy s hs =>
    linearODESolution_hasDerivAt h₀_mem hA_cont hy hs
  have hZ_init_eq : ∀ y : F, Z y h₀ = Z₀ y := fun y =>
    linearODESolution_init A a b' h₀ Z₀ y
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set E_T : ℝ := if M = 0 then β - α else (Real.exp (M * (β - α)) - 1) / M
    with hET_def
  set E_δ : ℝ := if M = 0 then 1 else Real.exp (M * (β - α)) with hEδ_def
  have hgb_eq : ∀ δ ε : ℝ,
      gronwallBound δ M ε (β - α) = δ * E_δ + ε * E_T := by
    intro δ ε
    by_cases hMeq : M = 0
    · have hEδ_val : E_δ = 1 := by rw [hEδ_def, if_pos hMeq]
      have hET_val : E_T = β - α := by rw [hET_def, if_pos hMeq]
      rw [hMeq, hEδ_val, hET_val, gronwallBound_K0]; ring
    · have hEδ_val : E_δ = Real.exp (M * (β - α)) := by
        rw [hEδ_def, if_neg hMeq]
      have hET_val : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, if_neg hMeq]
      rw [hEδ_val, hET_val, gronwallBound_of_K_ne_0 hMeq]
      field_simp
  have hET_nn : 0 ≤ E_T := by
    by_cases hMeq : M = 0
    · have : E_T = β - α := by rw [hET_def, if_pos hMeq]
      rw [this]; linarith
    · have : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, if_neg hMeq]
      rw [this]
      have hexp_ge : 1 ≤ Real.exp (M * (β - α)) :=
        Real.one_le_exp (mul_nonneg hM_nn hβα_nn)
      have : 0 ≤ Real.exp (M * (β - α)) - 1 := by linarith
      exact div_nonneg this hM_nn
  have hEδ_pos : 0 < E_δ := by
    by_cases hMeq : M = 0
    · have : E_δ = 1 := by rw [hEδ_def, if_pos hMeq]
      rw [this]; norm_num
    · have : E_δ = Real.exp (M * (β - α)) := by rw [hEδ_def, if_neg hMeq]
      rw [this]; exact Real.exp_pos _
  have hEδ_nn : 0 ≤ E_δ := hEδ_pos.le
  set c₁ : ℝ := c / (2 * E_δ) with hc₁_def
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]; positivity
  set c₂ : ℝ := c / (2 * (E_T + 1)) with hc₂_def
  have hET_inc : 0 < E_T + 1 := by linarith
  have hc₂_pos : 0 < c₂ := by
    rw [hc₂_def]; positivity
  have hEδ_ne : E_δ ≠ 0 := ne_of_gt hEδ_pos
  have hET_inc_ne : (E_T + 1 : ℝ) ≠ 0 := ne_of_gt hET_inc
  have h_bound_compose : c₁ * E_δ + c₂ * E_T ≤ c := by
    have h1 : c₁ * E_δ = c / 2 := by
      rw [hc₁_def, div_mul_eq_mul_div, mul_div_assoc]
      have : E_δ / (2 * E_δ) = 1 / 2 := by
        rw [div_eq_iff (by positivity)]; ring
      rw [this]; ring
    have h2 : c₂ * E_T ≤ c / 2 := by
      rw [hc₂_def]
      have hET_le : E_T ≤ E_T + 1 := by linarith
      have hstep : c / (2 * (E_T + 1)) * E_T ≤ c / (2 * (E_T + 1)) * (E_T + 1) :=
        mul_le_mul_of_nonneg_left hET_le (by positivity)
      have hfinal : c / (2 * (E_T + 1)) * (E_T + 1) = c / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        have : (E_T + 1) / (2 * (E_T + 1)) = 1 / 2 := by
          rw [div_eq_iff (by positivity)]; ring
        rw [this]; ring
      linarith
    linarith
  have hZ₀_at : HasFDerivAt Z₀ (fderiv ℝ Z₀ x) x := hZ₀_diff x hx
  have hZ₀_lit : (fun h : F => Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h) =o[𝓝 0]
      (fun h : F => h) :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hZ₀_at
  have hZ₀_bd_event : ∀ᶠ h : F in 𝓝 0,
      ‖Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h‖ ≤ c₁ * ‖h‖ :=
    (Asymptotics.isLittleO_iff.mp hZ₀_lit) hc₁_pos
  set ε₁ : ℝ := c₂ / (2 * (Q + 1)) with hε₁_def
  have hQ_inc : 0 < Q + 1 := by linarith
  have hε₁_pos : 0 < ε₁ := by rw [hε₁_def]; positivity
  obtain ⟨δ_tay, hδ_tay_pos, hδ_tay_le_δ₀, h_tay_bd⟩ := h_taylor ε₁ hε₁_pos
  set δ_pcs : ℝ := c₂ / (2 * (P * C_stab + 1)) with hδ_pcs_def
  have hPCS_inc : 0 < P * C_stab + 1 := by
    have : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
    linarith
  have hδ_pcs_pos : 0 < δ_pcs := by rw [hδ_pcs_def]; positivity
  set δ_force : ℝ := min δ_tay δ_pcs with hδ_force_def
  have hδ_force_pos : 0 < δ_force :=
    lt_min hδ_tay_pos hδ_pcs_pos
  have hδ_force_le_δ_tay : δ_force ≤ δ_tay := min_le_left _ _
  have hδ_force_le_δ_pcs : δ_force ≤ δ_pcs := min_le_right _ _
  have h_force_total : ∀ h : F, ‖h‖ ≤ δ_force →
      ε₁ * Q + P * C_stab * ‖h‖ ≤ c₂ := by
    intro h hh_le
    have h1 : ε₁ * Q ≤ c₂ / 2 := by
      rw [hε₁_def]
      have hQ_le : Q ≤ Q + 1 := by linarith
      have hQ1_pos : (0 : ℝ) < Q + 1 := hQ_inc
      have hstep : c₂ / (2 * (Q + 1)) * Q ≤ c₂ / (2 * (Q + 1)) * (Q + 1) :=
        mul_le_mul_of_nonneg_left hQ_le (by positivity)
      have hfinal : c₂ / (2 * (Q + 1)) * (Q + 1) = c₂ / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        field_simp
      linarith
    have h2 : P * C_stab * ‖h‖ ≤ c₂ / 2 := by
      have hh_le_δ_pcs : ‖h‖ ≤ δ_pcs := le_trans hh_le hδ_force_le_δ_pcs
      have hpcs_nn : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
      have : P * C_stab * ‖h‖ ≤ P * C_stab * δ_pcs :=
        mul_le_mul_of_nonneg_left hh_le_δ_pcs hpcs_nn
      have h_step2 : P * C_stab * δ_pcs ≤ c₂ / 2 := by
        rw [hδ_pcs_def]
        have hPCS_le : P * C_stab ≤ P * C_stab + 1 := by linarith
        have hPCS_pos : (0 : ℝ) < P * C_stab + 1 := hPCS_inc
        have hPCS_ne : (P * C_stab + 1 : ℝ) ≠ 0 := ne_of_gt hPCS_inc
        have hstep1 : P * C_stab * (c₂ / (2 * (P * C_stab + 1)))
            ≤ (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) :=
          mul_le_mul_of_nonneg_right hPCS_le (by positivity)
        have hfinal : (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) = c₂ / 2 := by
          rw [mul_div_assoc']
          field_simp
        linarith
      linarith
    linarith
  rw [Metric.eventually_nhds_iff]
  rw [Metric.eventually_nhds_iff] at hZ₀_bd_event
  obtain ⟨δ_init, hδ_init_pos, hδ_init_bd⟩ := hZ₀_bd_event
  set δ_final : ℝ := min δ_force δ_init with hδ_final_def
  have hδ_final_pos : 0 < δ_final := lt_min hδ_force_pos hδ_init_pos
  refine ⟨δ_final, hδ_final_pos, ?_⟩
  intro h hh_lt
  rw [dist_zero_right] at hh_lt
  have hh_le_force : ‖h‖ ≤ δ_force := le_of_lt (lt_of_lt_of_le hh_lt (min_le_left _ _))
  have hh_lt_init : dist h 0 < δ_init :=
    lt_of_lt_of_le (by rw [dist_zero_right]; exact hh_lt) (min_le_right _ _)
  have hh_le_δ₀ : ‖h‖ ≤ δ₀ :=
    le_trans (le_trans hh_le_force hδ_force_le_δ_tay) hδ_tay_le_δ₀
  have hh_le_δ_tay : ‖h‖ ≤ δ_tay := le_trans hh_le_force hδ_force_le_δ_tay
  have hdist_xh_x : dist (x + h) x = ‖h‖ := by
    rw [dist_eq_norm]; congr 1; abel
  have hxh_ball : x + h ∈ Metric.closedBall x δ₀ := by
    rw [Metric.mem_closedBall, hdist_xh_x]; exact hh_le_δ₀
  have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
  set R : ℝ → G := fun s => Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s
    with hR_def
  set Force : ℝ → G := fun s =>
    (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
      + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s)
    with hForce_def
  set Rderiv : ℝ → G := fun s => A x s (R s) + Force s with hRderiv_def
  have hR_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt R (Rderiv s) s := by
    intro s hs
    have h1 := hZ_deriv (x + h) hxh_U s hs
    have h2 := hZ_deriv x hx s hs
    have h3 := hW_deriv h s hs
    have hRderiv := (h1.sub h2).sub h3
    have h_eq :
        A (x + h) s (Z (x + h) s) - A x s (Z x s)
            - ((fderiv ℝ (fun y => A y s) x) h (Z x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x h s))
        = Rderiv s := by
      change _ = A x s (R s) + Force s
      have hRs : R s = Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s := rfl
      have hForce_val : Force s
          = (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
            + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s) := rfl
      rw [hRs, hForce_val]
      rw [show Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s
          = (Z (x + h) s - Z x s) + (-variationalSolution A a b' h₀ Z₀ x h s) by abel,
        ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
        ContinuousLinearMap.map_neg]
      rw [sub_apply, sub_apply,
        ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hRderiv
    exact hRderiv
  have hR_init : R h₀ = Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h := by
    change Z (x + h) h₀ - Z x h₀ - variationalSolution A a b' h₀ Z₀ x h h₀ = _
    rw [hZ_init_eq (x + h), hZ_init_eq x, hW_init_eq h]
  have hR_init_bd : ‖R h₀‖ ≤ c₁ * ‖h‖ := by
    rw [hR_init]; exact hδ_init_bd hh_lt_init
  have h_force_bd : ∀ s ∈ Set.Icc α β,
      ‖Force s‖ ≤ (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by
    intro s hs
    have h_tay := h_tay_bd h hh_le_δ_tay s hs
    have hZxh_bd : ‖Z (x + h) s‖ ≤ Q := hQ_bd' (x + h, s) ⟨hxh_ball, hs⟩
    have h_stab_s := h_stab h hh_le_δ₀ s hs
    have hP_s_bd : ‖fderiv ℝ (fun z => A z s) x‖ ≤ P := hDAx_bd s hs
    let diffA : G →L[ℝ] G :=
      A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h
    let dxA : F →L[ℝ] (G →L[ℝ] G) := fderiv ℝ (fun z => A z s) x
    let piece1 : G := diffA (Z (x + h) s)
    let piece2 : G := dxA h (Z (x + h) s - Z x s)
    have hp1 : ‖piece1‖ ≤ (ε₁ * Q) * ‖h‖ := by
      change ‖diffA (Z (x + h) s)‖ ≤ _
      have hop : ‖diffA (Z (x + h) s)‖ ≤ ‖diffA‖ * ‖Z (x + h) s‖ := diffA.le_opNorm _
      have hbd : ‖diffA‖ * ‖Z (x + h) s‖ ≤ (ε₁ * ‖h‖) * Q :=
        mul_le_mul h_tay hZxh_bd (norm_nonneg _) (by positivity)
      calc ‖diffA (Z (x + h) s)‖
          ≤ ‖diffA‖ * ‖Z (x + h) s‖ := hop
        _ ≤ (ε₁ * ‖h‖) * Q := hbd
        _ = (ε₁ * Q) * ‖h‖ := by ring
    have hp2 : ‖piece2‖ ≤ (P * C_stab * ‖h‖) * ‖h‖ := by
      change ‖dxA h (Z (x + h) s - Z x s)‖ ≤ _
      have hop1 : ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := (dxA h).le_opNorm _
      have hop2 : ‖dxA h‖ ≤ ‖dxA‖ * ‖h‖ := dxA.le_opNorm h
      have h2 : ‖dxA h‖ ≤ P * ‖h‖ :=
        le_trans hop2 (mul_le_mul_of_nonneg_right hP_s_bd (norm_nonneg _))
      have h3 : ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ ≤ (P * ‖h‖) * (C_stab * ‖h‖) :=
        mul_le_mul h2 h_stab_s (norm_nonneg _) (mul_nonneg hP_nn (norm_nonneg _))
      calc ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := hop1
        _ ≤ (P * ‖h‖) * (C_stab * ‖h‖) := h3
        _ = (P * C_stab * ‖h‖) * ‖h‖ := by ring
    change ‖piece1 + piece2‖ ≤ _
    calc ‖piece1 + piece2‖
        ≤ ‖piece1‖ + ‖piece2‖ := norm_add_le _ _
      _ ≤ (ε₁ * Q) * ‖h‖ + (P * C_stab * ‖h‖) * ‖h‖ := add_le_add hp1 hp2
      _ = (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by ring
  set ε_total : ℝ := ε₁ * Q + P * C_stab * ‖h‖ with hε_total_def
  have hε_total_nn : 0 ≤ ε_total := by
    rw [hε_total_def]
    have h1 : 0 ≤ ε₁ * Q := mul_nonneg hε₁_pos.le hQ_nn
    have h2 : 0 ≤ P * C_stab * ‖h‖ :=
      mul_nonneg (mul_nonneg hP_nn hC_stab_nn) (norm_nonneg _)
    linarith
  have hε_total_le_c₂ : ε_total ≤ c₂ := h_force_total h hh_le_force
  have hR_deriv_norm_bd : ∀ s ∈ Set.Icc α β,
      ‖Rderiv s‖ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by
    intro s hs
    have hAR : ‖A x s (R s)‖ ≤ M * ‖R s‖ := by
      have h1 : ‖A x s (R s)‖ ≤ ‖A x s‖ * ‖R s‖ := (A x s).le_opNorm _
      have h2 : ‖A x s‖ * ‖R s‖ ≤ M * ‖R s‖ :=
        mul_le_mul_of_nonneg_right (hAx_bd s hs) (norm_nonneg _)
      linarith
    have hFB : ‖Force s‖ ≤ ε_total * ‖h‖ := h_force_bd s hs
    have hR_val : Rderiv s = A x s (R s) + Force s := rfl
    rw [hR_val]
    calc ‖A x s (R s) + Force s‖
        ≤ ‖A x s (R s)‖ + ‖Force s‖ := norm_add_le _ _
      _ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by linarith
  have hR_cont : ContinuousOn R (Set.Icc α β) := fun s hs =>
    ((hR_deriv s (hIcc_sub hs)).continuousAt).continuousWithinAt
  have hRt_bd :
      ‖R t‖ ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) :=
    norm_le_gronwallBound_on_Icc hh₀_mem_Icc ht_mem_Icc
      (mul_nonneg hc₁_pos.le (norm_nonneg _)) hM_nn
      (mul_nonneg hε_total_nn (norm_nonneg _)) hR_cont
      (fun s hs => hR_deriv s (hIcc_sub hs)) hR_init_bd hR_deriv_norm_bd
  have h_final : ‖R t‖ ≤ c * ‖h‖ := by
    have hgb_evald : gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α)
        = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_eq _ _
    have h_step :
        (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T
          = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := by ring
    have h_ε_le : ε_total * E_T ≤ c₂ * E_T :=
      mul_le_mul_of_nonneg_right hε_total_le_c₂ hET_nn
    have h_combo :
        c₁ * E_δ + ε_total * E_T ≤ c₁ * E_δ + c₂ * E_T :=
      add_le_add_right h_ε_le _
    have h_bound_final :
        ‖h‖ * (c₁ * E_δ + ε_total * E_T) ≤ ‖h‖ * c := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact h_combo.trans h_bound_compose
    calc ‖R t‖
        ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) := hRt_bd
      _ = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_evald
      _ = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := h_step
      _ ≤ ‖h‖ * c := h_bound_final
      _ = c * ‖h‖ := by ring
  have h_clm_apply :
      (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h
        = variationalSolution A a b' h₀ Z₀ x h t :=
    variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht h
  change ‖linearODESolution A a b' h₀ Z₀ (x + h) t
        - linearODESolution A a b' h₀ Z₀ x t
        - (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h‖
      ≤ c * ‖h‖
  rw [h_clm_apply]
  change ‖R t‖ ≤ c * ‖h‖
  exact h_final

end VariationalSolution

end Poincare.ODE.LocalFlow

end
