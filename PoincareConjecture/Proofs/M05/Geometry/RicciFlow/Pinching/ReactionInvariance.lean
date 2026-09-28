
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PoincareConjecture.Proofs.M05.Analysis.Calculus.Nonnegative
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Barrier
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Reaction












namespace Poincare.HamiltonIvey

open Set
open scoped Topology


private theorem trace_reaction_lower_bound {lam mu nu : ℝ} :
    2 * (lam + mu + nu) ^ 2 / 3 ≤
      (lam ^ 2 + mu * nu) + (mu ^ 2 + lam * nu) + (nu ^ 2 + lam * mu) := by
  nlinarith [sq_nonneg (lam - mu), sq_nonneg (mu - nu), sq_nonneg (lam - nu)]

private theorem horizontal_boundary_strict
    {t : ℝ} (ht : 0 ≤ t) {lam mu nu dS : ℝ}
    (hS : lam + mu + nu = -3 / (1 + t))
    (hdS : dS = (lam ^ 2 + mu * nu) + (mu ^ 2 + lam * nu) +
      (nu ^ 2 + lam * mu)) :
    3 / (1 + t) ^ 2 < dS := by
  have hden : 0 < 1 + t := by linarith
  have htrace := trace_reaction_lower_bound (lam := lam) (mu := mu) (nu := nu)
  rw [hS] at htrace
  rw [hdS]
  have hp : 0 < 3 / (1 + t) ^ 2 := by positivity
  have hsq : 2 * (-3 / (1 + t)) ^ 2 / 3 = 6 / (1 + t) ^ 2 := by
    field_simp
    ring
  rw [hsq] at htrace
  have hden2 : 0 < (1 + t) ^ 2 := sq_pos_of_pos hden
  have htrace' := (div_le_iff₀ hden2).mp htrace
  apply (div_lt_iff₀ hden2).2
  nlinarith






theorem reaction_trace_lower_bound
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu S : ℝ → ℝ}
    (hScont : ContinuousOn S (Icc a b))
    (hSval : ∀ t ∈ Icc a b, S t = lam t + mu t + nu t)
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt S
      ((lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t)) (Ici t) t)
    (hinit : -3 / (1 + a) ≤ S a) :
    ∀ t ∈ Icc a b, -3 / (1 + t) ≤ S t := by
  let r : ℝ → ℝ := fun t => -3 / (1 + t)
  have hr {t : ℝ} (ht : 0 ≤ t) : HasDerivAt r (3 / (1 + t) ^ 2) t := by
    have hden : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa only [id_eq, add_comm] using (hasDerivAt_id t).const_add 1
    change HasDerivAt (fun s : ℝ => -3 / (1 + s)) (3 / (1 + t) ^ 2) t
    have hder := (hasDerivAt_const t (-3)).div hden (by linarith)
    have hfun : (fun _ : ℝ => (-3 : ℝ)) / (fun s : ℝ => 1 + s) =
        (fun s => -3 / (1 + s)) := by
      funext s
      simp only [Pi.div_apply]
    rw [hfun] at hder
    have hval : (0 * (1 + t) - (-3) * 1) / (1 + t) ^ 2 =
        3 / (1 + t) ^ 2 := by ring
    rw [hval] at hder
    exact hder
  have hrcont : ContinuousOn r (Icc a b) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro t ht
      linarith [ha, ht.1]
  have hbound : ∀ t ∈ Ico a b, r t = S t →
      3 / (1 + t) ^ 2 <
        (lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
          (nu t ^ 2 + lam t * mu t) := by
    intro t ht hEq
    apply horizontal_boundary_strict (ht := ha.trans ht.1)
    · have hsum := hSval t ⟨ht.1, ht.2.le⟩
      simpa [r] using (hEq.trans hsum).symm
    · rfl
  have hle := image_le_of_deriv_right_lt_deriv_boundary'
    (f := r) (f' := fun t => 3 / (1 + t) ^ 2)
    (B := S) (B' := fun t =>
      (lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t))
    hrcont
    (fun t ht => (hr (ha.trans ht.1)).hasDerivWithinAt)
    (by simpa [r] using hinit)
    hScont
    (fun t ht => hderiv t ht)
    hbound
  intro t ht
  exact hle ht

private theorem logBarrier_comp_deriv
    {X : ℝ → ℝ} {t dX : ℝ} (ht : 0 ≤ t) (hX : 0 < X t)
    (hXd : HasDerivAt X dX t) :
    HasDerivAt (fun s => logBarrier s (X s))
      (dX * (Real.log (X t) + Real.log (1 + t) - 2) + X t / (1 + t)) t := by
  have hlog : HasDerivAt (fun s => Real.log (X s)) (dX / X t) t :=
    (hXd.log (ne_of_gt hX))
  have htime : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t := by
    have hden : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa only [id_eq, add_comm] using (hasDerivAt_id t).const_add 1
    have hder :=
      (Real.hasDerivAt_log (x := 1 + t) (by linarith : (1 + t) ≠ 0)).comp t hden
    have hfun : Real.log ∘ (fun s : ℝ => 1 + s) =
        (fun s => Real.log (1 + s)) := by
      funext s
      rfl
    rw [hfun] at hder
    have hval : (1 + t)⁻¹ * 1 = 1 / (1 + t) := by simp [one_div]
    rw [hval] at hder
    exact hder
  have hprod := hXd.mul ((hlog.add htime).sub_const 3)
  change HasDerivAt (X * (fun s => Real.log (X s) + Real.log (1 + s) - 3)) _ t
  have hprod' : HasDerivAt (X * (fun s =>
      Real.log (X s) + Real.log (1 + s) - 3))
      (dX * (Real.log (X t) + Real.log (1 + t) - 3) +
        X t * (dX / X t + 1 / (1 + t))) t := by
    exact hprod
  convert hprod' using 1 <;> field_simp [ne_of_gt hX] <;> ring

private theorem logarithmic_boundary_strict
    {t : ℝ} (ht : 0 ≤ t) {lam mu nu S X : ℝ → ℝ} {dS dX : ℝ}
    (hmu : mu t ≤ lam t) (hnu : nu t ≤ mu t)
    (hXval : X t = -nu t) (hSval : S t = lam t + mu t + nu t)
    (hS : HasDerivAt S dS t) (hX : HasDerivAt X dX t)
    (hdS : dS = (lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
      (nu t ^ 2 + lam t * mu t))
    (hdX : dX = -(nu t) ^ 2 - mu t * lam t)
    (hXpos : 0 < X t) (hcutX : cutoff t ≤ X t)
    (hEq : logBarrier t (X t) = S t) :
    deriv (fun s => logBarrier s (X s)) t < deriv S t := by
  have hXfirst : 1 / (1 + t) < X t :=
    (cutoff_gt_first ht).trans_le hcutX
  have hbar := pinchingReactionBarrier
    (lam := lam t) (mu := mu t) (nu := nu t) (S := S) (X := X)
    hmu hnu hXval hSval hS hX (by
      rw [hXval]
      nlinarith [hdS]) (by
      rw [hXval]
      nlinarith [hdX]) hXpos
  have hW : X t ≤ deriv (fun s => S s / X s - Real.log (X s)) t := hbar
  have hW' := ((hS.div hX (ne_of_gt hXpos)).sub
    (hX.log (ne_of_gt hXpos))).deriv
  change X t ≤ deriv (S / X - fun y => Real.log (X y)) t at hW
  rw [hW'] at hW
  have hF := logBarrier_comp_deriv ht hXpos hX
  rw [hF.deriv]
  rw [hS.deriv]
  have hden : 0 < X t := hXpos
  have htime : 0 < 1 + t := by linarith
  have hstrict : 1 / (1 + t) < X t := hXfirst
  have hEq' : S t = X t * (Real.log (X t) + Real.log (1 + t) - 3) := by
    simpa [logBarrier] using hEq.symm
  have hW'' : X t ≤
      (X t * dS - (S t + X t) * dX) / X t ^ 2 := by
    calc
      X t ≤ (dS * X t - S t * dX) / X t ^ 2 - dX / X t := hW
      _ = (X t * dS - (S t + X t) * dX) / X t ^ 2 := by
        field_simp [ne_of_gt hXpos]
        ring
  have hWmul : X t ^ 3 ≤ X t * dS - (S t + X t) * dX := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (le_div_iff₀ (sq_pos_of_pos hXpos)).mp hW''
  have hWdiv : X t ^ 2 ≤
      (X t * dS - (S t + X t) * dX) / X t := by
    apply (le_div_iff₀ hXpos).2
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hWmul
  have hWlin : X t ^ 2 ≤ dS -
      (Real.log (X t) + Real.log (1 + t) - 2) * dX := by
    calc
      X t ^ 2 ≤ (X t * dS - (S t + X t) * dX) / X t := hWdiv
      _ = dS - (Real.log (X t) + Real.log (1 + t) - 2) * dX := by
        rw [hEq']
        field_simp [ne_of_gt hXpos]
        ring
  have hXsq : X t / (1 + t) < X t ^ 2 := by
    apply (div_lt_iff₀ htime).2
    have hmul : 1 < X t * (1 + t) := (div_lt_iff₀ htime).mp hstrict
    have hprodpos : 0 < X t * (X t * (1 + t) - 1) :=
      mul_pos hXpos (sub_pos.mpr hmul)
    nlinarith
  linarith







theorem reaction_log_branch_invariance
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu S X : ℝ → ℝ}
    (hScont : ContinuousOn S (Icc a b))
    (hFcont : ContinuousOn (fun t => logBarrier t (X t)) (Icc a b))
    (hSval : ∀ t ∈ Icc a b, S t = lam t + mu t + nu t)
    (hXval : ∀ t ∈ Icc a b, X t = -nu t)
    (hord : ∀ t ∈ Icc a b, mu t ≤ lam t ∧ nu t ≤ mu t)
    (hSderiv : ∀ t ∈ Ico a b, HasDerivAt S
      ((lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t)) t)
    (hXderiv : ∀ t ∈ Ico a b, HasDerivAt X
      (-(nu t) ^ 2 - mu t * lam t) t)
    (hcut : ∀ t ∈ Icc a b, cutoff t ≤ X t)
    (hinit : (S a, X a) ∈ scalarRegion a) :
    ∀ t ∈ Icc a b, (S t, X t) ∈ scalarRegion t := by
  have htrace : ∀ t ∈ Icc a b, -3 / (1 + t) ≤ S t := by
    apply reaction_trace_lower_bound ha hab hScont hSval
    · intro t ht
      exact (hSderiv t ht).hasDerivWithinAt
    · change -3 / (1 + a) ≤ S a ∧ _ at hinit
      exact hinit.1
  have hFle : ∀ t ∈ Icc a b, logBarrier t (X t) ≤ S t := by
    have haF : logBarrier a (X a) ≤ S a := by
      have hm := (mem_scalarRegion_iff ha).mp hinit
      simpa [clippedBarrier, max_eq_right (hcut a ⟨le_rfl, hab⟩)] using hm
    have hbound : ∀ t ∈ Ico a b,
        logBarrier t (X t) = S t →
          (-(nu t) ^ 2 - mu t * lam t) *
              (Real.log (X t) + Real.log (1 + t) - 2) + X t / (1 + t) <
            ((lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
              (nu t ^ 2 + lam t * mu t)) := by
      intro t ht hEq
      rcases hord t ⟨ht.1, ht.2.le⟩ with ⟨hmu, hnu⟩
      have hb := logarithmic_boundary_strict (ha.trans ht.1) hmu hnu
        (hXval t ⟨ht.1, ht.2.le⟩) (hSval t ⟨ht.1, ht.2.le⟩)
        (hSderiv t ht) (hXderiv t ht) rfl rfl
        ((cutoff_pos (ha.trans ht.1)).trans_le (hcut t ⟨ht.1, ht.2.le⟩))
        (hcut t ⟨ht.1, ht.2.le⟩)
        hEq
      rw [(logBarrier_comp_deriv (ha.trans ht.1)
        ((cutoff_pos (ha.trans ht.1)).trans_le (hcut t ⟨ht.1, ht.2.le⟩))
        (hXderiv t ht)).deriv, (hSderiv t ht).deriv] at hb
      exact hb
    exact image_le_of_deriv_right_lt_deriv_boundary'
      (f := fun t => logBarrier t (X t))
      (f' := fun t => (-(nu t) ^ 2 - mu t * lam t) *
        (Real.log (X t) + Real.log (1 + t) - 2) + X t / (1 + t))
      (B := S)
      (B' := fun t =>
        (lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
          (nu t ^ 2 + lam t * mu t))
      hFcont
      (fun t ht => (logBarrier_comp_deriv (ha.trans ht.1)
        ((cutoff_pos (ha.trans ht.1)).trans_le (hcut t ⟨ht.1, ht.2.le⟩))
        (hXderiv t ht)).hasDerivWithinAt)
      haF hScont (fun t ht => (hSderiv t ht).hasDerivWithinAt) hbound
  intro t ht
  rw [mem_scalarRegion_iff (ha.trans ht.1)]
  rw [clippedBarrier, max_eq_right (hcut t ht)]
  exact hFle t ht

private theorem reaction_trace_lower_bound_interior
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu S : ℝ → ℝ}
    (hScont : ContinuousOn S (Icc a b))
    (hSval : ∀ t ∈ Icc a b, S t = lam t + mu t + nu t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt S
      ((lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t)) t)
    (hinit : -3 / (1 + a) ≤ S a) :
    ∀ t ∈ Icc a b, -3 / (1 + t) ≤ S t := by
  have hZ := Poincare.nonneg_of_deriv_pos_on_neg hab
    (f := fun t => (1 + t) * S t + 3)
    ((continuousOn_const.add continuousOn_id).mul hScont |>.add continuousOn_const)
    (by have := (div_le_iff₀ (by linarith : 0 < 1 + a)).mp hinit
        nlinarith)
    (by
      intro t ht hneg
      let dS := (lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t)
      have htime : 0 < 1 + t := by linarith [ht.1]
      have hSt : S t < 0 := by nlinarith
      have htrace : 2 * S t ^ 2 / 3 ≤ dS := by
        rw [hSval t (Ioo_subset_Icc_self ht)]
        exact trace_reaction_lower_bound
      refine ⟨1 * S t + (1 + t) * dS + 0, ?_, ?_⟩
      · simpa using (((hasDerivAt_id t).const_add 1).mul (hderiv t ht)).add_const 3
      · have hscaled := mul_le_mul_of_nonneg_left htrace htime.le
        have hprod := mul_pos (neg_pos.mpr hSt) (neg_pos.mpr hneg)
        nlinarith)
  intro t ht
  apply (div_le_iff₀ (by linarith [ht.1] : 0 < 1 + t)).mpr
  nlinarith [hZ t ht]

private theorem normalized_barrier_nonneg_iff {t s y : ℝ} (hy : 0 < y) :
    0 ≤ s / y - Real.log y - Real.log (1 + t) + 3 ↔ logBarrier t y ≤ s := by
  rw [logBarrier]
  constructor
  · intro h
    have := (le_div_iff₀ hy).mp
      (show Real.log y + Real.log (1 + t) - 3 ≤ s / y by linarith)
    nlinarith
  · intro h
    have := (le_div_iff₀ hy).mpr
      (show (Real.log y + Real.log (1 + t) - 3) * y ≤ s by nlinarith)
    linarith






theorem reaction_invariance
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Set.Icc a b))
    (hmu : ContinuousOn mu (Set.Icc a b))
    (hnu : ContinuousOn nu (Set.Icc a b))
    (hord : ∀ t ∈ Set.Icc a b, mu t ≤ lam t ∧ nu t ≤ mu t)
    (hdlam : ∀ t ∈ Set.Ioo a b,
      HasDerivAt lam (lam t ^ 2 + mu t * nu t) t)
    (hdmu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt mu (mu t ^ 2 + lam t * nu t) t)
    (hdnu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt nu (nu t ^ 2 + lam t * mu t) t)
    (hinit : (lam a + mu a + nu a, max (-nu a) 0) ∈ scalarRegion a) :
    ∀ t ∈ Set.Icc a b,
      (lam t + mu t + nu t, max (-nu t) 0) ∈ scalarRegion t := by
  let S : ℝ → ℝ := fun t => lam t + mu t + nu t
  let X : ℝ → ℝ := fun t => -nu t
  let Y : ℝ → ℝ := fun t => max (cutoff t) (X t)
  let W : ℝ → ℝ := fun t => S t / Y t - Real.log (Y t) - Real.log (1 + t) + 3
  have htime : ∀ t ∈ Icc a b, 0 < 1 + t := by
    intro t ht
    linarith [ht.1]
  have hSc : ContinuousOn S (Icc a b) := (hlam.add hmu).add hnu
  have hXc : ContinuousOn X (Icc a b) := hnu.neg
  have hSd : ∀ t ∈ Ioo a b, HasDerivAt S
      ((lam t ^ 2 + mu t * nu t) + (mu t ^ 2 + lam t * nu t) +
        (nu t ^ 2 + lam t * mu t)) t :=
    fun t ht => ((hdlam t ht).add (hdmu t ht)).add (hdnu t ht)
  have htrace : ∀ t ∈ Icc a b, -3 / (1 + t) ≤ S t :=
    reaction_trace_lower_bound_interior ha hab hSc (fun _ _ => rfl) hSd hinit.1
  have hcutc : ContinuousOn cutoff (Icc a b) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun t ht => (htime t ht).ne')
  have hYc : ContinuousOn Y (Icc a b) := hcutc.sup hXc
  have hYpos : ∀ t ∈ Icc a b, 0 < Y t := fun t ht =>
    (cutoff_pos (ha.trans ht.1)).trans_le (le_max_left _ _)
  have hWc : ContinuousOn W (Icc a b) :=
    (((hSc.div hYc (fun t ht => (hYpos t ht).ne')).sub
      (hYc.log (fun t ht => (hYpos t ht).ne'))).sub
      ((continuousOn_const.add continuousOn_id).log
        (fun t ht => (htime t ht).ne'))).add continuousOn_const
  have hWiff : ∀ t ∈ Icc a b,
      0 ≤ W t ↔ (S t, max (X t) 0) ∈ scalarRegion t := by
    intro t ht
    rw [mem_scalarRegion_iff (ha.trans ht.1)]
    have hmax : max (cutoff t) (max (X t) 0) = Y t := by
      rw [← max_assoc, max_eq_left (hYpos t ht).le]
    simpa only [W, clippedBarrier, hmax] using
      normalized_barrier_nonneg_iff (s := S t) (t := t) (hYpos t ht)
  have hWa : 0 ≤ W a := (hWiff a ⟨le_rfl, hab⟩).mpr hinit
  have hWnonneg := Poincare.nonneg_of_deriv_pos_on_neg hab hWc hWa (by
    intro t ht hneg
    have htcc := Ioo_subset_Icc_self ht
    have ht0 : 0 ≤ t := ha.trans htcc.1
    have hcutlt : cutoff t < X t := by
      by_contra h
      have hYeq : Y t = cutoff t := max_eq_left (le_of_not_gt h)
      have hbar : logBarrier t (Y t) ≤ S t := by
        rw [hYeq, (cutoff_spec ht0).2.1]
        exact htrace t htcc
      exact (not_le_of_gt hneg)
        ((normalized_barrier_nonneg_iff (hYpos t htcc)).mpr hbar)
    have hYeq : Y t = -nu t := max_eq_right hcutlt.le
    have hlocal : Y =ᶠ[𝓝 t] X := by
      have hlt := (hcutc.continuousAt (Icc_mem_nhds ht.1 ht.2)).eventually_lt
        (hXc.continuousAt (Icc_mem_nhds ht.1 ht.2)) hcutlt
      filter_upwards [hlt] with s hs using max_eq_right hs.le
    have hYd : HasDerivAt Y (-(nu t ^ 2 + lam t * mu t)) t :=
      (hdnu t ht).neg.congr_of_eventuallyEq hlocal
    have hD := ((hSd t ht).div hYd (hYpos t htcc).ne').sub
      (hYd.log (hYpos t htcc).ne')
    have hlogtime : HasDerivAt (fun s : ℝ => Real.log (1 + s))
        (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_id t).const_add 1).log (htime t htcc).ne'
    have hbar := pinchingReactionBarrier (hord t htcc).1 (hord t htcc).2
      hYeq (show S t = lam t + mu t + nu t from rfl) (hSd t ht) hYd
      (by rw [hYeq]; ring) (by rw [hYeq]; ring) (hYpos t htcc)
    have hfirst : 1 / (1 + t) < Y t :=
      (cutoff_spec ht0).1.trans_le (le_max_left _ _)
    change Y t ≤ deriv (S / Y - fun s => Real.log (Y s)) t at hbar
    rw [hD.deriv] at hbar
    exact ⟨_, (hD.sub hlogtime).add_const 3, by linarith⟩)
  intro t ht
  exact (hWiff t ht).mp (hWnonneg t ht)

end Poincare.HamiltonIvey
