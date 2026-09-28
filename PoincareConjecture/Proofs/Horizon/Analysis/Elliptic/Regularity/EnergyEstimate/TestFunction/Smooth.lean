import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Poincare.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem contDiff_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Poincare.Analysis.Sobolev.diffQuot k h v) := by
  have h_translate :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => y + h • EuclideanSpace.single k 1) :=
    contDiff_id.add contDiff_const
  have h_comp :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => v (y + h • EuclideanSpace.single k 1)) :=
    hv.comp h_translate
  have h_sub :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => v (y + h • EuclideanSpace.single k 1) - v y) :=
    h_comp.sub hv
  have h_div :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) := by
    have heq :
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) =
          fun y : E =>
            h⁻¹ • (v (y + h • EuclideanSpace.single k 1) - v y) := by
      funext y
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    exact h_sub.const_smul h⁻¹
  have heq_fun :
      (Poincare.Analysis.Sobolev.diffQuot k h v) =
        fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h := by
    funext y
    exact Poincare.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh v y
  rw [heq_fun]
  exact h_div

omit [NeZero d] in
theorem contDiff_nirenbergTestFunction_aux
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Poincare.Analysis.Sobolev.diffQuot k (-h)
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y)) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
  have h_diffQuot_u :
      ContDiff ℝ (⊤ : ℕ∞)
        (Poincare.Analysis.Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  have h_prod :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) :=
    h_eta_sq.mul h_diffQuot_u
  exact contDiff_diffQuot_of_contDiff (d := d) h_prod k hnh

omit [NeZero d] in
theorem hasCompactSupport_translate_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Poincare.Analysis.Sobolev.translate k h v) := by
  let φ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have heq :
      Poincare.Analysis.Sobolev.translate k h v = v ∘ φ := by
    funext x
    rfl
  rw [heq]
  exact hv.comp_homeomorph φ

omit [NeZero d] in
theorem hasCompactSupport_diffQuot_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Poincare.Analysis.Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [Poincare.Analysis.Sobolev.diffQuot_zero_h]
    exact HasCompactSupport.zero
  · have heq :
        Poincare.Analysis.Sobolev.diffQuot k h v =
          (h⁻¹ : ℝ) •
            (Poincare.Analysis.Sobolev.translate k h v - v) := by
      funext x
      rw [Poincare.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hh v x]
      change (v (x + h • EuclideanSpace.single k 1) - v x) / h =
        h⁻¹ • (v (x + h • EuclideanSpace.single k 1) - v x)
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    have h_translate :
        HasCompactSupport
          (Poincare.Analysis.Sobolev.translate k h v) :=
      hasCompactSupport_translate_of_hasCompactSupport (d := d) hv k h
    have h_diff :
        HasCompactSupport
          (Poincare.Analysis.Sobolev.translate k h v - v) :=
      h_translate.sub hv
    exact h_diff.smul_left

noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : E → ℝ :=
  Poincare.Analysis.Sobolev.diffQuot k (-h)
    (fun y : E => η y ^ 2 *
      Poincare.Analysis.Sobolev.diffQuot k h u y)

omit [NeZero d] in
theorem contDiff_nirenbergTestFunction
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  exact contDiff_nirenbergTestFunction_aux (d := d) hη hu k hh

omit [NeZero d] in
theorem hasCompactSupport_nirenbergTestFunction
    {η u : E → ℝ} (hη_supp : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y
      ring
    rw [heq]
    exact hη_supp.mul_right
  have h_prod_supp :
      HasCompactSupport
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) :=
    h_eta_sq_supp.mul_right
  exact hasCompactSupport_diffQuot_of_hasCompactSupport
    (d := d) h_prod_supp k (-h)

omit [NeZero d] in
private lemma support_eta_sq_subset
    (η : E → ℝ) :
    Function.support (fun y : E => η y ^ 2) ⊆ Function.support η := by
  intro y hy
  by_contra hyη
  rw [Function.notMem_support] at hyη
  apply hy
  change η y ^ 2 = 0
  rw [hyη]
  simp

omit [NeZero d] in
private lemma support_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    Function.support
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) ⊆
      Function.support η := by
  intro y hy
  have hsq_ne : η y ^ 2 ≠ 0 := by
    intro hsq
    apply hy
    change η y ^ 2 *
        Poincare.Analysis.Sobolev.diffQuot k h u y = 0
    rw [hsq, zero_mul]
  intro hyη
  apply hsq_ne
  rw [hyη]
  simp

omit [NeZero d] in
private lemma tsupport_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) ⊆
      tsupport η := by
  exact closure_mono (support_eta_sq_diffQuot_subset (d := d) η u k h)

omit [NeZero d] in
theorem tsupport_nirenbergTestFunction_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      Metric.cthickening |h| (tsupport η) := by
  unfold nirenbergTestFunction
  set g : E → ℝ := fun y : E => η y ^ 2 *
    Poincare.Analysis.Sobolev.diffQuot k h u y with hg_def
  have h_thick_closed : IsClosed (Metric.cthickening |h| (tsupport η)) :=
    isClosed_cthickening
  have h_self_subset_thick : tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    self_subset_cthickening _
  have h_shift_in_thick :
      ∀ y₀ ∈ tsupport η,
        y₀ - (-h) • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
    intro y₀ hy₀
    refine Metric.mem_cthickening_of_dist_le _ y₀ |h| (tsupport η) hy₀ ?_
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have hdist_eq :
        dist (y₀ - (-h) • EuclideanSpace.single k 1) y₀ =
          ‖(-h) • EuclideanSpace.single k (1 : ℝ)‖ := by
      rw [dist_eq_norm]
      have :
          (y₀ - (-h) • EuclideanSpace.single k 1) - y₀ =
            -((-h) • EuclideanSpace.single k 1) := by
        rw [sub_right_comm, sub_self, zero_sub]
      rw [this, norm_neg]
    rw [hdist_eq]
    rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs, abs_neg]
  have h_supp_subset :
      Function.support
          (Poincare.Analysis.Sobolev.diffQuot k (-h) g) ⊆
        Metric.cthickening |h| (tsupport η) := by
    intro x hx
    have hx_ne : Poincare.Analysis.Sobolev.diffQuot k (-h) g x ≠ 0 :=
      hx
    by_cases hh : h = 0
    · subst hh
      exfalso
      apply hx_ne
      have hzeroNeg : (-(0 : ℝ)) = 0 := neg_zero
      rw [hzeroNeg]
      change Poincare.Analysis.Sobolev.diffQuot k 0 g x = 0
      rw [Poincare.Analysis.Sobolev.diffQuot_zero_h]
      rfl
    · have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
      rw [Poincare.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hnh g x] at hx_ne
      have hnum_ne : g (x + (-h) • EuclideanSpace.single k 1) - g x ≠ 0 := by
        intro hnum
        apply hx_ne
        rw [hnum, zero_div]
      have h_or :
          g (x + (-h) • EuclideanSpace.single k 1) ≠ 0 ∨ g x ≠ 0 := by
        by_contra hboth
        rw [not_or] at hboth
        obtain ⟨hb1, hb2⟩ := hboth
        have hb1' : g (x + (-h) • EuclideanSpace.single k 1) = 0 :=
          not_not.mp hb1
        have hb2' : g x = 0 := not_not.mp hb2
        apply hnum_ne
        rw [hb1', hb2', sub_zero]
      cases h_or with
      | inl h1 =>
        have h_in_supp_g :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support g :=
          h1
        have h_in_supp_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_supp_g
        have h_in_tsupp_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
          subset_closure h_in_supp_η
        have h_x_eq :
            x =
              (x + (-h) • EuclideanSpace.single k 1) -
                (-h) • EuclideanSpace.single k 1 := by
          rw [add_sub_cancel_right]
        rw [h_x_eq]
        exact h_shift_in_thick _ h_in_tsupp_η
      | inr h2 =>
        have h_in_supp_g : x ∈ Function.support g := h2
        have h_in_supp_η : x ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_supp_g
        have h_in_tsupp_η : x ∈ tsupport η := subset_closure h_in_supp_η
        exact h_self_subset_thick h_in_tsupp_η
  exact (closure_minimal h_supp_subset h_thick_closed)

omit [NeZero d] in
private lemma hasFDerivAt_translate (k : Fin d) (h : ℝ) (x : E) :
    HasFDerivAt
      (fun y : E => y + h • EuclideanSpace.single k 1)
      (ContinuousLinearMap.id ℝ E) x := by
  exact (hasFDerivAt_id x).add_const _

omit [NeZero d] in
theorem fderiv_diffQuot_apply_eq_diffQuot_partial
    {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (Poincare.Analysis.Sobolev.diffQuot k h g) x)
      (EuclideanSpace.single j 1) =
      Poincare.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x := by
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hg_at : ∀ y : E, HasFDerivAt g (fderiv ℝ g y) y :=
    fun y => (hg_diff y).hasFDerivAt
  have h_translate_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => z + h • EuclideanSpace.single k 1)
        (ContinuousLinearMap.id ℝ E) y :=
    fun y => hasFDerivAt_translate (d := d) k h y
  have h_comp_at : ∀ y : E,
      HasFDerivAt (fun z : E => g (z + h • EuclideanSpace.single k 1))
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1)) y := by
    intro y
    have hcomp :=
      (hg_at (y + h • EuclideanSpace.single k 1)).comp y (h_translate_at y)
    have heq :
        ((fderiv ℝ g (y + h • EuclideanSpace.single k 1)).comp
          (ContinuousLinearMap.id ℝ E)) =
          fderiv ℝ g (y + h • EuclideanSpace.single k 1) := by
      ext z
      rfl
    rw [heq] at hcomp
    exact hcomp
  have h_diff_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => g (z + h • EuclideanSpace.single k 1) - g z)
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1) - fderiv ℝ g y) y := by
    intro y
    exact (h_comp_at y).sub (hg_at y)
  have h_div_at : ∀ y : E,
      HasFDerivAt
        (fun z : E =>
          (g (z + h • EuclideanSpace.single k 1) - g z) / h)
        (h⁻¹ • (fderiv ℝ g (y + h • EuclideanSpace.single k 1) -
          fderiv ℝ g y)) y := by
    intro y
    have hcs := (h_diff_at y).const_smul h⁻¹
    have heq_fun :
        (h⁻¹ • fun z : E => g (z + h • EuclideanSpace.single k 1) - g z) =
          fun z : E =>
            (g (z + h • EuclideanSpace.single k 1) - g z) / h := by
      funext z
      change h⁻¹ • (g (z + h • EuclideanSpace.single k 1) - g z) =
        (g (z + h • EuclideanSpace.single k 1) - g z) / h
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq_fun] at hcs
    exact hcs
  have heq_diffQuot :
      (Poincare.Analysis.Sobolev.diffQuot k h g) =
        fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h := by
    funext y
    exact Poincare.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh g y
  rw [heq_diffQuot]
  have h_at : HasFDerivAt
      (fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h)
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
        fderiv ℝ g x)) x := h_div_at x
  rw [h_at.fderiv]
  set ej : E := EuclideanSpace.single j 1 with hej
  have h_apply :
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
          fderiv ℝ g x)) ej =
        h⁻¹ • ((fderiv ℝ g (x + h • EuclideanSpace.single k 1)) ej -
          (fderiv ℝ g x) ej) := by
    rw [smul_apply]
    rw [sub_apply]
  rw [h_apply]
  rw [Poincare.Analysis.Sobolev.diffQuot_apply_of_ne
    (d := d) k hh _ x]
  rw [div_eq_inv_mul, smul_eq_mul]

omit [NeZero d] in
theorem fderiv_eta_sq_times_diffQuot_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) x)
      (EuclideanSpace.single j 1) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Poincare.Analysis.Sobolev.diffQuot k h u x +
      η x ^ 2 *
        Poincare.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x := by
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hη_sq_diff : Differentiable ℝ (fun y : E => η y ^ 2) :=
    (hη.pow 2).differentiable (by simp)
  have h_diffQuot_u_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Poincare.Analysis.Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  have h_diffQuot_u_diff :
      Differentiable ℝ
        (Poincare.Analysis.Sobolev.diffQuot k h u) :=
    h_diffQuot_u_smooth.differentiable (by simp)
  set ej : E := EuclideanSpace.single j 1 with hej
  have h_prod :
      fderiv ℝ
          (fun y : E => η y ^ 2 *
            Poincare.Analysis.Sobolev.diffQuot k h u y) x =
        η x ^ 2 •
          fderiv ℝ
            (Poincare.Analysis.Sobolev.diffQuot k h u) x +
          Poincare.Analysis.Sobolev.diffQuot k h u x •
            fderiv ℝ (fun y : E => η y ^ 2) x := by
    exact fderiv_fun_mul (hη_sq_diff x) (h_diffQuot_u_diff x)
  rw [h_prod]
  rw [add_apply,
      smul_apply,
      smul_apply]
  have hη_pow_fd :
      fderiv ℝ (fun y : E => η y ^ 2) x =
        ((2 : ℕ) • (η x) ^ ((2 : ℕ) - 1)) • fderiv ℝ η x :=
    fderiv_fun_pow 2 (hη_diff x)
  rw [hη_pow_fd]
  rw [smul_apply]
  have hpow1 : (η x) ^ ((2 : ℕ) - 1) = η x := by
    norm_num
  rw [hpow1]
  have h_fderiv_diffQuot :
      (fderiv ℝ
          (Poincare.Analysis.Sobolev.diffQuot k h u) x) ej =
        Poincare.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x :=
    fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hu k j hh x
  rw [h_fderiv_diffQuot]
  have h_two_smul : ((2 : ℕ) • η x) = 2 * η x := by
    rw [two_smul]
    ring
  rw [h_two_smul]
  change η x ^ 2 *
        Poincare.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x +
      Poincare.Analysis.Sobolev.diffQuot k h u x *
        (2 * η x * (fderiv ℝ η x) ej) =
      2 * η x * (fderiv ℝ η x) ej *
        Poincare.Analysis.Sobolev.diffQuot k h u x +
      η x ^ 2 *
        Poincare.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x
  ring

omit [NeZero d] in
theorem fderiv_nirenbergTestFunction_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ (nirenbergTestFunction k h η u) x)
        (EuclideanSpace.single j 1) =
      Poincare.Analysis.Sobolev.diffQuot k (-h)
        (fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            Poincare.Analysis.Sobolev.diffQuot k h u y +
          η y ^ 2 *
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y)
        x := by
  unfold nirenbergTestFunction
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hg_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          Poincare.Analysis.Sobolev.diffQuot k h u y) := by
    have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h_diffQuot_u :
        ContDiff ℝ (⊤ : ℕ∞)
          (Poincare.Analysis.Sobolev.diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact h_eta_sq.mul h_diffQuot_u
  rw [fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hg_smooth k j hnh x]
  have h_pointwise :
      (fun y : E =>
          (fderiv ℝ
              (fun z : E => η z ^ 2 *
                Poincare.Analysis.Sobolev.diffQuot k h u z) y)
            (EuclideanSpace.single j 1)) =
        fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            Poincare.Analysis.Sobolev.diffQuot k h u y +
          η y ^ 2 *
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y := by
    funext y
    exact fderiv_eta_sq_times_diffQuot_apply (d := d) hη hu k j hh y
  rw [h_pointwise]

example {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k 1 η u) :=
  contDiff_nirenbergTestFunction hη hu k one_ne_zero

example {η : E → ℝ} (hη_supp : HasCompactSupport η) (u : E → ℝ)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) :=
  hasCompactSupport_nirenbergTestFunction hη_supp k h

end Poincare.Analysis.Sobolev.NirenbergTestFunction
