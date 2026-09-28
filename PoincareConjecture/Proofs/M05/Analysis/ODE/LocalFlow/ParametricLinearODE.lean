import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.ParameterDerivative

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
private theorem linearODESolution_partial_t_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (fun p : F × ℝ => A p.1 p.2 (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn
      (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have h_app_cont : Continuous fun q : (G →L[ℝ] G) × G => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have h_pair_cont : ContinuousOn
      (fun p : F × ℝ => (A p.1 p.2, linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.prodMk hA_cont hZ_cont
  exact h_app_cont.comp_continuousOn h_pair_cont

open Classical in
private theorem variationalW_clm_continuousOn
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U) :
    ContinuousOn
      (fun p : F × ℝ =>
        if hx : p.1 ∈ U then
          if ht : p.2 ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0
        else 0)
      (U ×ˢ Set.Ioo a b') := by
  rw [continuousOn_clm_apply]
  intro v
  have h_eq : ∀ p ∈ U ×ˢ Set.Ioo a b',
      (if hx : p.1 ∈ U then
        if ht : p.2 ∈ Set.Ioo a b' then
          variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
        else 0
      else 0) v =
      variationalSolution A a b' h₀ Z₀ p.1 v p.2 := by
    intro ⟨x, t⟩ ⟨hxU, htI⟩
    change (if hx : x ∈ U then if ht : t ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0 else 0) v = _
    rw [dif_pos hxU, dif_pos htI]
    exact variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hxU htI v
  refine ContinuousOn.congr ?_ h_eq
  have hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U :=
    (ContinuousLinearMap.apply ℝ G v).continuous.comp_continuousOn hDZ₀_cont
  exact variationalW_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v hZ₀'_cont

private theorem linearODESolution_hasFDerivAt_joint
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
    {x₀ : F} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b') :
    HasFDerivAt (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      ((variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
          (A x₀ t₀ (linearODESolution A a b' h₀ Z₀ x₀ t₀))))
      (x₀, t₀) := by
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  set v₀ := A x₀ t₀ (Z x₀ t₀) with hv₀_def
  set L_x := variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀
  set L := L_x.coprod (ContinuousLinearMap.toSpanSingleton ℝ v₀)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hx_param := linearODESolution_hasFDerivAt_param h₀_mem hU hA_cont hDA_cont
    hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx₀ ht₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hx_param
  have hx_param_bd := hx_param.bound (show (0 : ℝ) < c / 2 by linarith)
  obtain ⟨δ_x, hδ_x_pos, hδ_x_bd⟩ := Metric.eventually_nhds_iff.mp hx_param_bd
  have ht_partial_cont :
      ContinuousOn (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (U ×ˢ Set.Ioo a b') :=
    linearODESolution_partial_t_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hx₀t₀_mem : (x₀, t₀) ∈ U ×ˢ Set.Ioo a b' := ⟨hx₀, ht₀⟩
  have ht_partial_cont_at : ContinuousAt
      (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (x₀, t₀) :=
    (ht_partial_cont (x₀, t₀) hx₀t₀_mem).continuousAt (hS_open.mem_nhds hx₀t₀_mem)
  rw [Metric.continuousAt_iff] at ht_partial_cont_at
  obtain ⟨δ_t, hδ_t_pos, hδ_t_bd⟩ := ht_partial_cont_at (c / 2) (by linarith)
  have h_add_nhds : ∀ᶠ p : F × ℝ in 𝓝 (0, 0),
      x₀ + p.1 ∈ U ∧ t₀ + p.2 ∈ Set.Ioo a b' := by
    have h1 : ∀ᶠ q : F in 𝓝 0, x₀ + q ∈ U := by
      have : Continuous (fun q : F => x₀ + q) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx₀)
    have h2 : ∀ᶠ r : ℝ in 𝓝 0, t₀ + r ∈ Set.Ioo a b' := by
      have : Continuous (fun r : ℝ => t₀ + r) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using isOpen_Ioo.mem_nhds ht₀)
    rw [nhds_prod_eq]
    exact h1.prod_mk h2
  obtain ⟨δ₀, hδ₀_pos, hδ₀_bd⟩ := Metric.eventually_nhds_iff.mp h_add_nhds
  set δ := min δ₀ (min δ_x δ_t) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos (lt_min hδ_x_pos hδ_t_pos)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun ⟨h, s⟩ h_dist => ?_⟩
  simp only [dist_zero_right] at h_dist
  have hh_lt : ‖h‖ < δ := lt_of_le_of_lt (le_max_left _ _) h_dist
  have hs_lt : ‖s‖ < δ := lt_of_le_of_lt (le_max_right _ _) h_dist
  have hh_lt_δ₀ : ‖h‖ < δ₀ := lt_of_lt_of_le hh_lt (min_le_left _ _)
  have hs_lt_δ₀ : ‖s‖ < δ₀ := lt_of_lt_of_le hs_lt (min_le_left _ _)
  have hh_lt_δx : ‖h‖ < δ_x :=
    lt_of_lt_of_le hh_lt ((min_le_right _ _).trans (min_le_left _ _))
  have hhs_lt_δt : max ‖h‖ ‖s‖ < δ_t :=
    lt_of_lt_of_le h_dist ((min_le_right _ _).trans (min_le_right _ _))
  have hprod_mem : x₀ + h ∈ U ∧ t₀ + s ∈ Set.Ioo a b' := by
    have h_dist_pair : dist (h, s) (0, 0) < δ₀ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
      exact max_lt hh_lt_δ₀ hs_lt_δ₀
    exact hδ₀_bd h_dist_pair
  obtain ⟨hxh_U, hts_Ioo⟩ := hprod_mem
  change ‖uncurry Z ((x₀, t₀) + (h, s)) - uncurry Z (x₀, t₀) - L (h, s)‖ ≤ c * ‖(h, s)‖
  simp only [uncurry, Prod.mk_add_mk]
  have hL_eq : L (h, s) = L_x h + s • v₀ := by
    simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hL_eq]
  have h_split :
      Z (x₀ + h) (t₀ + s) - Z x₀ t₀ - (L_x h + s • v₀)
        = (Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
          + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h) := by abel
  rw [h_split]
  calc ‖(Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
        + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h)‖
      ≤ ‖Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀‖
        + ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖(h, s)‖ + c / 2 * ‖(h, s)‖ := by
        apply add_le_add
        · have hZ_deriv_at : ∀ r ∈ Set.Ioo a b',
              HasDerivAt (Z (x₀ + h) ·) (A (x₀ + h) r (Z (x₀ + h) r)) r :=
            fun r hr => linearODESolution_hasDerivAt h₀_mem hA_cont hxh_U hr
          set χ : ℝ → G := fun r => Z (x₀ + h) r - (r - t₀) • v₀ with hχ_def
          have hχ_diff : ∀ r ∈ Set.Ioo a b', DifferentiableAt ℝ χ r := by
            intro r hr
            exact (hZ_deriv_at r hr).differentiableAt.sub
              (((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀).differentiableAt
          have hχ_deriv : ∀ r ∈ Set.Ioo a b',
              deriv χ r = A (x₀ + h) r (Z (x₀ + h) r) - v₀ := by
            intro r hr
            have hd : HasDerivAt χ (A (x₀ + h) r (Z (x₀ + h) r) - v₀) r := by
              have hd1 := hZ_deriv_at r hr
              have hd2 : HasDerivAt (fun r => (r - t₀) • v₀) v₀ r := by
                have h_base := ((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀
                refine (h_base.congr_of_eventuallyEq ?_).congr_deriv ?_
                · exact Filter.Eventually.of_forall fun y => by
                    change (y - t₀) • v₀ = (y - t₀) • v₀
                    rfl
                · simp
              exact hd1.sub hd2
            exact hd.deriv
          have h_uIcc_sub : Set.uIcc t₀ (t₀ + s) ⊆ Set.Ioo a b' := by
            intro r hr
            rw [Set.mem_uIcc] at hr
            constructor
            · rcases hr with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ht₀.1, hts_Ioo.1]
            · rcases hr with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [ht₀.2, hts_Ioo.2]
          have hχ_deriv_bd : ∀ r ∈ Set.uIcc t₀ (t₀ + s), ‖deriv χ r‖ ≤ c / 2 := by
            intro r hr
            rw [hχ_deriv r (h_uIcc_sub hr)]
            have h_r_bound : ‖r - t₀‖ ≤ ‖s‖ := by
              rw [Set.mem_uIcc] at hr
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
              rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
              · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
            have h_dist_prod : dist (x₀ + h, r) (x₀, t₀) < δ_t := by
              rw [Prod.dist_eq, dist_eq_norm, show x₀ + h - x₀ = h from add_sub_cancel_left _ _,
                dist_eq_norm]
              exact lt_of_le_of_lt (max_le_max le_rfl h_r_bound) hhs_lt_δt
            have := hδ_t_bd h_dist_prod
            rw [dist_eq_norm] at this
            exact le_of_lt this
          have hχ_diff_uI : ∀ r ∈ Set.uIcc t₀ (t₀ + s),
              DifferentiableAt ℝ χ r :=
            fun r hr => hχ_diff r (h_uIcc_sub hr)
          have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le
            (𝕜 := ℝ)
            hχ_diff_uI
            hχ_deriv_bd
            (convex_uIcc t₀ (t₀ + s))
            (Set.left_mem_uIcc) (Set.right_mem_uIcc)
          have hχ_diff_eq :
              χ (t₀ + s) - χ t₀
                = Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀ := by
            simp [hχ_def]; ring_nf; abel
          rw [← hχ_diff_eq]
          have hs_eq : ‖t₀ + s - t₀‖ = ‖s‖ := by rw [add_sub_cancel_left]
          rw [hs_eq] at h_mvt
          calc ‖χ (t₀ + s) - χ t₀‖
              ≤ c / 2 * ‖s‖ := h_mvt
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_snd_le (h, s)) (by linarith)
        · have h_param_bd : ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ ≤ c / 2 * ‖h‖ := by
            have := hδ_x_bd (show dist h 0 < δ_x by rwa [dist_zero_right])
            have hLx : L_x h = variationalSolution A a b' h₀ Z₀ x₀ h t₀ := by
              exact variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀ h
            rw [hLx]
            simpa [hZ_def] using this
          calc ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖
              ≤ c / 2 * ‖h‖ := h_param_bd
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_fst_le (h, s)) (by linarith)
    _ = c * ‖(h, s)‖ := by ring

private theorem linearODESolution_contDiffOn_one
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
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) :
    ContDiffOn ℝ 1
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) _ _
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
  have hdiff : DifferentiableOn ℝ (Function.uncurry Z) (U ×ˢ Set.Ioo a b') := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    exact (linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont hA_diff
      hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
  have htop : (0 : WithTop ℕ∞) = ⊤ →
      AnalyticOn ℝ (Function.uncurry Z) (U ×ˢ Set.Ioo a b') := by
    intro h_absurd
    exact absurd h_absurd (by simp)
  have hfderiv_cont : ContDiffOn ℝ 0 (fderiv ℝ (Function.uncurry Z))
      (U ×ˢ Set.Ioo a b') := by
    rw [contDiffOn_zero]
    have h_coprod_bilin : Continuous
        (fun (p : (F →L[ℝ] G) × (ℝ →L[ℝ] G)) => p.1.coprod p.2) :=
      (ContinuousLinearMap.coprodEquivL ℝ).continuous
    have h_clm_cont : ContinuousOn
        (fun p : F × ℝ =>
          if hx : p.1 ∈ U then
            if ht : p.2 ∈ Set.Ioo a b' then
              variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
            else 0
          else 0)
        (U ×ˢ Set.Ioo a b') :=
      variationalW_clm_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont hDZ₀_cont
    have h_toSpan_cont : ContinuousOn
        (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
          (A p.1 p.2 (Z p.1 p.2)))
        (U ×ˢ Set.Ioo a b') :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp_continuousOn
        (linearODESolution_partial_t_continuousOn h₀_mem hU hA_cont hZ₀_cont)
    have h_formula_cont :=
      h_coprod_bilin.comp_continuousOn (h_clm_cont.prodMk h_toSpan_cont)
    apply h_formula_cont.congr
    intro p hp
    obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
    have h_eq : (if hx' : p.1 ∈ U then
        if ht' : p.2 ∈ Set.Ioo a b' then
          variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
        else 0
      else 0) = variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
      rw [dif_pos hx, dif_pos ht]
    change fderiv ℝ (uncurry Z) p
        = ((if hx' : p.1 ∈ U then
              if ht' : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
              else 0
            else 0).coprod
            (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
    rw [h_eq, hZ_def]
    conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
    exact (linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont
      hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv
  exact ⟨hdiff, htop, hfderiv_cont⟩

omit [CompleteSpace G] in
private theorem inhomogAugmentedCoeff_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {U : Set F} {a b' : ℝ}
    (hA : ContDiffOn ℝ n (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb : ContDiffOn ℝ n (Function.uncurry b) (U ×ˢ Set.Ioo a b')) :
    ContDiffOn ℝ n (Function.uncurry (inhomogAugmentedCoeff A b))
      (U ×ˢ Set.Ioo a b') := by
  have h_first : ContDiffOn ℝ n
      (fun p : F × ℝ => (A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ))
      (U ×ˢ Set.Ioo a b') :=
    hA.clm_comp contDiffOn_const
  have h_second : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
    have h_smul_cont : ContDiff ℝ n
        (fun y : G => (ContinuousLinearMap.snd ℝ G ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (G × ℝ) G
        (ContinuousLinearMap.snd ℝ G ℝ)).contDiff
    exact h_smul_cont.comp_contDiffOn hb
  have h_sum : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)))
      (U ×ˢ Set.Ioo a b') := h_first.add h_second
  have h_prodL : ContDiff ℝ n
      (fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) => q.1.prod q.2) :=
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × ℝ) (F := G) (G := ℝ) ℝ).contDiff
  have h_pair : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
        (0 : (G × ℝ) →L[ℝ] ℝ)))
      (U ×ˢ Set.Ioo a b') := h_sum.prodMk contDiffOn_const
  exact h_prodL.comp_contDiffOn h_pair

omit [CompleteSpace G] in
private theorem extract_C1_hypotheses
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {n : ℕ}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (↑(n + 1) : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (↑(n + 1) : ℕ∞) Z₀ U) :
    ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b') ∧
    ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b') ∧
    (∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y) ∧
    ContinuousOn Z₀ U ∧
    ContinuousOn (fun x => fderiv ℝ Z₀ x) U ∧
    (∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
    hA.of_le (by norm_cast; omega)
  have hZ₀_ge1 : ContDiffOn ℝ 1 Z₀ U := hZ₀.of_le (by norm_cast; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA_ge1.continuousOn
  · have h_fderiv_cont : ContinuousOn (fderiv ℝ (Function.uncurry A))
        (U ×ˢ Set.Ioo a b') :=
      hA_ge1.continuousOn_fderiv_of_isOpen hS_open le_rfl
    have h_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
        fderiv ℝ (fun y => A y p.2) p.1
          = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
      intro ⟨x, t⟩ ⟨hx, ht⟩
      have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
        ext y; simp [Function.uncurry]
      have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
        apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
          (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩)
      rw [h_eq_comp]
      rw [fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
      simp [hasFDerivAt_prodMk_left x t |>.fderiv]
    refine (h_fderiv_cont.clm_comp continuousOn_const).congr h_eq
  · intro y hy s hs
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (y, s) := by
      apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
        (y, s) (Set.mem_prod.mpr ⟨hy, hs⟩)).differentiableAt
      exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hy, hs⟩)
    have h_diff_partial : DifferentiableAt ℝ (fun z => A z s) y := by
      have : (fun z => A z s) = Function.uncurry A ∘ (fun z => (z, s)) := by
        ext z; simp [Function.uncurry]
      rw [this]
      exact h_diffA.comp y (hasFDerivAt_prodMk_left y s).differentiableAt
    exact h_diff_partial.hasFDerivAt
  · exact hZ₀_ge1.continuousOn
  · exact hZ₀_ge1.continuousOn_fderiv_of_isOpen hU le_rfl
  · intro y hy
    exact ((hZ₀_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0) y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt

omit [CompleteSpace G] in
private theorem variationalForcing_contDiffOn_of_Z_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} {h₀ : ℝ} {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (n + 1) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ : ContDiffOn ℝ n (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b'))
    (v : F) :
    ContDiffOn ℝ n
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have h_fderivA : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry A))
      (U ×ˢ Set.Ioo a b') :=
    hA.fderiv_of_isOpen hS_open le_rfl
  have h_partial : ContDiffOn ℝ n
      (fun p : F × ℝ => (fderiv ℝ (Function.uncurry A) p).comp
        (ContinuousLinearMap.inl ℝ F ℝ))
      (U ×ˢ Set.Ioo a b') :=
    h_fderivA.clm_comp contDiffOn_const
  have h_eval_v : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v)
      (U ×ˢ Set.Ioo a b') :=
    h_partial.clm_apply contDiffOn_const
  have h_agree : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      (fderiv ℝ (fun y => A y p.2) p.1)
        = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by simp)
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
      exact ((hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
        (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        (hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩))
    have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
      ext y; simp [Function.uncurry]
    rw [h_eq_comp, fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
    simp [hasFDerivAt_prodMk_left x t |>.fderiv]
  have h_forcing_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t) p
        = ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v
            (linearODESolution A a b' h₀ Z₀ p.1 p.2) := by
    intro ⟨x, t⟩ hp
    simp only [Function.uncurry, variationalForcing]
    rw [h_agree (x, t) hp]
  exact (h_eval_v.clm_apply hZ).congr h_forcing_eq

end VariationalSolution

theorem linearODESolution_contDiffOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (n : ℕ)
    (hA : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (n : ℕ∞) Z₀ U) :
    ContDiffOn ℝ (n : ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  induction n generalizing G with
  | zero =>
    exact (contDiffOn_zero.mpr
      (linearODESolution_continuousOn h₀_mem hU hA.continuousOn hZ₀.continuousOn))
  | succ n ih =>
    have hA_n : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by norm_cast; omega)
    have hZ₀_n : ContDiffOn ℝ (n : ℕ∞) Z₀ U := hZ₀.of_le (by norm_cast; omega)
    have hZ_n : ContDiffOn ℝ (n : ℕ∞)
        (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
      ih hA_n hZ₀_n
    have ⟨hA_cont, hDA_cont, hA_diff, hZ₀_cont, hDZ₀_cont, hZ₀_diff⟩ :=
      extract_C1_hypotheses hU hA hZ₀
    set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
    set S := (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) with hS_def
    have hS_open : IsOpen S := hU.prod isOpen_Ioo
    suffices h_goal : ContDiffOn ℝ ((↑(↑n : ℕ∞) : WithTop ℕ∞) + 1) (Function.uncurry Z) S by
      exact_mod_cast h_goal
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
    refine ⟨?_, ?_, ?_⟩
    · intro ⟨x, t⟩ ⟨hx, ht⟩
      exact (linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont hA_diff
        hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
    · intro h_absurd
      exact absurd h_absurd WithTop.coe_ne_top
    · have h_AZ_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) S :=
        hA_n.clm_apply hZ_n
      have h_toSpan_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
            (A p.1 p.2 (Z p.1 p.2))) S :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).contDiff.comp_contDiffOn
          h_AZ_n
      have h_varW_v_n : ∀ v : F, ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => variationalSolution A a b' h₀ Z₀ p.1 v p.2) S := by
        intro v
        have h_forcing_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
            S :=
          variationalForcing_contDiffOn_of_Z_contDiffOn hU (by exact_mod_cast hA) hZ_n v
        have hZ₀_fderiv_n : ContDiffOn ℝ (↑n : ℕ∞) (fderiv ℝ Z₀) U :=
          hZ₀.fderiv_of_isOpen hU (by norm_cast)
        have h_augIC_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) U :=
          (hZ₀_fderiv_n.clm_apply contDiffOn_const).prodMk contDiffOn_const
        have h_Ahat_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (inhomogAugmentedCoeff A
              (fun y t => variationalForcing A a b' h₀ Z₀ y v t))) S :=
          inhomogAugmentedCoeff_contDiffOn hA_n h_forcing_n
        have h_aug_sol_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (linearODESolution
              (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
              a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))))) S :=
          ih (G := G × ℝ) h_Ahat_n h_augIC_n
        have h_fst_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun p : F × ℝ =>
              (linearODESolution
                (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
                a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) p.1 p.2).1) S :=
          contDiff_fst.comp_contDiffOn h_aug_sol_n
        exact h_fst_n.congr (fun _ _ => rfl)
      have h_clm_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0)
          S := by
        rw [contDiffOn_clm_apply]
        intro v'
        refine (h_varW_v_n v').congr (fun p hp => ?_)
        obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
        simp only [dif_pos hx, dif_pos ht]
        exact (variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx ht v').symm
      have h_coprod_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            (if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
          S := by
        exact (ContinuousLinearMap.coprodEquivL ℝ
          (E := F) (F := ℝ) (G := G)).contDiff.comp_contDiffOn
          (h_clm_n.prodMk h_toSpan_n)
      refine h_coprod_n.congr (fun p hp => ?_)
      obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
      have h_eq : (if hx' : p.1 ∈ U then
          if ht' : p.2 ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
          else 0
        else 0) = variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
        rw [dif_pos hx, dif_pos ht]
      change fderiv ℝ (Function.uncurry Z) p
          = ((if hx' : p.1 ∈ U then
                if ht' : p.2 ∈ Set.Ioo a b' then
                  variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
                else 0
              else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
      rw [h_eq, hZ_def]
      conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
      exact (linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont
        hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv

section CInfinityRegularity

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem linearODESolution_contDiffOn_top
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z₀ U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  rw [contDiffOn_infty]
  intro k
  exact linearODESolution_contDiffOn h₀_mem hU k
    (hA.of_le (by exact_mod_cast le_top)) (hZ₀.of_le (by exact_mod_cast le_top))

end CInfinityRegularity

end Poincare.ODE.LocalFlow

end
