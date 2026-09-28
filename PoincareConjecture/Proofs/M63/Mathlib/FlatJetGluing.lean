import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise

set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasDerivAt.piecewise_Iic {f g : ℝ → E} {c : ℝ} {v : E}
    (hf : HasDerivAt f v c) (hg : HasDerivAt g v c) (hfg : f c = g c) :
    HasDerivAt ((Iic c).piecewise f g) v c := by
  have hl : HasDerivWithinAt ((Iic c).piecewise f g) v (Iic c) c :=
    hf.hasDerivWithinAt.congr_of_mem (fun y hy => by simp [hy]) (by simp)
  have hr : HasDerivWithinAt ((Iic c).piecewise f g) v (Ici c) c := by
    apply hg.hasDerivWithinAt.congr_of_mem _ (by simp)
    intro y hy
    by_cases hle : y ≤ c
    · have hyc : y = c := le_antisymm hle hy
      subst y
      simp [hfg]
    · simp [hle]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

theorem contDiffAt_piecewise_Iic_of_iteratedDeriv_eq
    {f g : ℝ → E} {c : ℝ} (k : ℕ)
    (hf : ContDiffAt ℝ k f c) (hg : ContDiffAt ℝ k g c)
    (hjet : ∀ i ≤ k, iteratedDeriv i f c = iteratedDeriv i g c) :
    ContDiffAt ℝ k ((Iic c).piecewise f g) c := by
  induction k generalizing f g with
  | zero =>
      obtain ⟨u, hu, hfu⟩ := contDiffAt_zero.mp hf
      obtain ⟨v, hv, hgv⟩ := contDiffAt_zero.mp hg
      have hfg : f c = g c := by simpa only [iteratedDeriv_zero] using hjet 0 le_rfl
      refine contDiffAt_zero.mpr ⟨u ∩ v, inter_mem hu hv, ?_⟩
      apply ContinuousOn.piecewise
      · intro y hy
        have hyc : y = c := by simpa only [frontier_Iic, mem_singleton_iff] using hy.2
        simpa only [hyc] using hfg
      · exact hfu.mono (fun _ hy => hy.1.1)
      · exact hgv.mono (fun _ hy => hy.1.2)
  | succ k ih =>
      have hf' : ContDiffAt ℝ k (deriv f) c := hf.derivWithin (by simp)
      have hg' : ContDiffAt ℝ k (deriv g) c := hg.derivWithin (by simp)
      have hj' (i : ℕ) (hi : i ≤ k) :
          iteratedDeriv i (deriv f) c = iteratedDeriv i (deriv g) c := by
        simpa only [iteratedDeriv_succ'] using hjet (i + 1) (Nat.succ_le_succ hi)
      let d : ℝ → E := (Iic c).piecewise (deriv f) (deriv g)
      have hd : ContDiffAt ℝ k d c := ih hf' hg' hj'
      have hvalue : f c = g c := by
        simpa only [iteratedDeriv_zero] using hjet 0 (Nat.zero_le _)
      have hfirst : deriv f c = deriv g c := by
        simpa only [iteratedDeriv_one] using hjet 1 (Nat.succ_le_succ (Nat.zero_le _))
      have hnear : ∀ᶠ y in 𝓝 c, HasDerivAt ((Iic c).piecewise f g) (d y) y := by
        filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
        have hfd := (hfy.differentiableAt (by simp)).hasDerivAt
        have hgd := (hgy.differentiableAt (by simp)).hasDerivAt
        rcases lt_trichotomy y c with hlt | heq | hgt
        · have he : (Iic c).piecewise f g =ᶠ[𝓝 y] f := by
            filter_upwards [Iio_mem_nhds hlt] with z hz
            simp [(show z < c from hz).le]
          simpa only [d, piecewise, mem_Iic, if_pos hlt.le] using
            hfd.congr_of_eventuallyEq he
        · subst y
          have hgd' : HasDerivAt g (deriv f c) c := by rw [hfirst]; exact hgd
          simpa only [d, piecewise, mem_Iic, if_pos le_rfl] using
            hfd.piecewise_Iic hgd' hvalue
        · have he : (Iic c).piecewise f g =ᶠ[𝓝 y] g := by
            filter_upwards [Ioi_mem_nhds hgt] with z hz
            simp [not_le.mpr (show c < z from hz)]
          simpa only [d, piecewise, mem_Iic, if_neg (not_le.mpr hgt)] using
            hgd.congr_of_eventuallyEq he
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun y => ContinuousLinearMap.toSpanSingleton ℝ (d y),
        ⟨{y | HasDerivAt ((Iic c).piecewise f g) (d y) y}, hnear,
          fun _ hy => hy.hasFDerivAt⟩, ?_⟩
      exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff.contDiffAt.comp c hd

theorem contDiffAt_infty_piecewise_Iic_of_iteratedDeriv_eq
    {f g : ℝ → E} {c : ℝ}
    (hf : ContDiffAt ℝ ∞ f c) (hg : ContDiffAt ℝ ∞ g c)
    (hjet : ∀ i : ℕ, iteratedDeriv i f c = iteratedDeriv i g c) :
    ContDiffAt ℝ ∞ ((Iic c).piecewise f g) c := by
  apply contDiffAt_infty.mpr
  intro k
  exact contDiffAt_piecewise_Iic_of_iteratedDeriv_eq k
    (hf.of_le (by exact_mod_cast le_top (a := (k : ℕ∞))))
    (hg.of_le (by exact_mod_cast le_top (a := (k : ℕ∞)))) (fun i _ => hjet i)

theorem iteratedDeriv_scomp_eq_zero_of_flat
    {G : ℝ → E} {phi : ℝ → ℝ} {c : ℝ}
    (hG : ContDiffAt ℝ ∞ G (phi c)) (hphi : ContDiffAt ℝ ∞ phi c)
    (hflat : ∀ i : ℕ, 0 < i → iteratedDeriv i phi c = 0)
    {i : ℕ} (hi : 0 < i) : iteratedDeriv i (G ∘ phi) c = 0 := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hG hphi
    (by exact_mod_cast le_top (a := (i : ℕ∞)))]
  apply Finset.sum_eq_zero
  intro p _
  have hz : (∏ j, iteratedDeriv (p.partSize j) phi c) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ ⟨0, p.length_pos hi⟩)
      (hflat _ (p.partSize_pos _))
  rw [hz, zero_smul]
