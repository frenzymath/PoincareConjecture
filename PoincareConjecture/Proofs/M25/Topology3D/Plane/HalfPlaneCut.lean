import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem snd_pos_of_fixed_strip {E : Type*} [TopologicalSpace E]
    (F : (E × ℝ) ≃ₜ (E × ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hfix : ∀ x : E × ℝ, |x.2| < ε → F x = x)
    (x : E × ℝ) (hx : 0 < x.2) : 0 < (F x).2 := by
  let v := min x.2 (ε / 2)
  have hv : 0 < v := lt_min hx (half_pos hε)
  have hvy : v ≤ x.2 := min_le_left _ _
  have hve : v < ε := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
  let k : ℝ → ℝ := fun s => (F (x.1, s)).2
  have hk : Continuous k :=
    continuous_snd.comp (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hkv : k v = v := congrArg Prod.snd (hfix (x.1, v) (by
    simpa only [abs_of_pos hv] using hve))
  by_contra hn
  have hy : k x.2 ≤ 0 := le_of_not_gt hn
  obtain ⟨w, hw, hzero⟩ := intermediate_value_Icc' hvy hk.continuousOn
    (show (0 : ℝ) ∈ Icc (k x.2) (k v) from ⟨hy, by rw [hkv]; exact hv.le⟩)
  let r : E × ℝ := ((F (x.1, w)).1, 0)
  have hFr : F r = r := hfix r (by simpa only [r, abs_zero] using hε)
  have heqr : F (x.1, w) = r := Prod.ext rfl hzero
  have heq : F (x.1, w) = F r := heqr.trans hFr.symm
  have hwzero : w = 0 := congrArg Prod.snd (F.injective heq)
  exact (ne_of_gt (lt_of_lt_of_le hv hw.1)) hwzero




theorem exists_upper_halfSpace_diffeomorph_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => F p.1 p.2))
    (hFi : ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => (F p.1).symm p.2))
    {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z x, |x.2| < ε → F z x = x)
    {K : Set (E × ℝ)} (hK : IsCompact K)
    (hfixed : ∀ z x, x ∉ K → F z x = x) :
    ∃ G : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => (G p.1).symm p.2) ∧
      (∀ z x, 0 ≤ x.2 → G z x = F z x) ∧
      (∀ z x, x.2 ≤ 0 → G z x = x) ∧
      (∀ z x, 0 ≤ x.2 → (G z).symm x = (F z).symm x) ∧
      (∀ z x, x.2 ≤ 0 → (G z).symm x = x) ∧
      (∀ z x, x ∉ K → G z x = x ∧ (G z).symm x = x) ∧
      ∀ z, HasCompactSupport (fun x => G z x - x) ∧
        HasCompactSupport (fun x => (G z).symm x - x) := by
  classical
  have hstripi (z : ℝ) (x : E × ℝ) (hx : |x.2| < ε) : (F z).symm x = x := by
    have hh := congrArg (F z).symm (hstrip z x hx)
    simpa only [Diffeomorph.symm_apply_apply] using hh.symm
  have hnonneg (J : (E × ℝ) ≃ₜ (E × ℝ))
      (hJ : ∀ x : E × ℝ, |x.2| < ε → J x = x)
      (x : E × ℝ) (hx : 0 ≤ x.2) : 0 ≤ (J x).2 := by
    rcases eq_or_lt_of_le hx with heq | hpos
    · rw [hJ x (by rw [← heq, abs_zero]; exact hε)]
      exact hx
    · exact (snd_pos_of_fixed_strip J hε hJ x hpos).le
  let f : ℝ → (E × ℝ) → (E × ℝ) := fun z x => if 0 ≤ x.2 then F z x else x
  let g : ℝ → (E × ℝ) → (E × ℝ) := fun z x => if 0 ≤ x.2 then (F z).symm x else x
  have hleft (z : ℝ) : LeftInverse (g z) (f z) := by
    intro x
    by_cases hx : 0 ≤ x.2
    · have hp : 0 ≤ (F z x).2 := hnonneg (F z).toHomeomorph (hstrip z) x hx
      dsimp only [f, g]
      rw [if_pos hx, if_pos hp, Diffeomorph.symm_apply_apply]
    · simp only [f, g, if_neg hx]
  have hright (z : ℝ) : LeftInverse (f z) (g z) := by
    intro x
    by_cases hx : 0 ≤ x.2
    · have hp : 0 ≤ ((F z).symm x).2 :=
        hnonneg (F z).symm.toHomeomorph (hstripi z) x hx
      dsimp only [f, g]
      rw [if_pos hx, if_pos hp, Diffeomorph.apply_symm_apply]
    · simp only [f, g, if_neg hx]
  have hcut (U : ℝ → (E × ℝ) → (E × ℝ))
      (hU : ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => U p.1 p.2))
      (hUi : ∀ z x, |x.2| < ε → U z x = x) :
      ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => if 0 ≤ p.2.2 then U p.1 p.2 else p.2) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.2.2
    · apply hU.contDiffAt.congr_of_eventuallyEq
      have ho : IsOpen {q : ℝ × (E × ℝ) | 0 < q.2.2} :=
        isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
      filter_upwards [ho.mem_nhds hp] with q hq
      exact if_pos hq.le
    · have hs : ContDiffAt ℝ ∞ (Prod.snd : ℝ × (E × ℝ) → E × ℝ) p :=
        contDiff_snd.contDiffAt
      apply hs.congr_of_eventuallyEq
      have ho : IsOpen {q : ℝ × (E × ℝ) | q.2.2 < ε} :=
        isOpen_lt (continuous_snd.comp continuous_snd) continuous_const
      have hpe : p.2.2 < ε := lt_of_le_of_lt (le_of_not_gt hp) hε
      filter_upwards [ho.mem_nhds hpe] with q hq
      split_ifs with hh
      · exact hUi q.1 q.2 (by rwa [abs_of_nonneg hh])
      · rfl
  have hf : ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => f p.1 p.2) := hcut _ hF hstrip
  have hg : ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => g p.1 p.2) := hcut _ hFi hstripi
  let G : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)) := fun z =>
    { toEquiv :=
        { toFun := f z
          invFun := g z
          left_inv := hleft z
          right_inv := hright z }
      contMDiff_toFun := (hf.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hg.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  have hlower (U : ℝ → (E × ℝ) → (E × ℝ))
      (hUi : ∀ z x, |x.2| < ε → U z x = x)
      (z : ℝ) (x : E × ℝ) (hx : x.2 ≤ 0) :
      (if 0 ≤ x.2 then U z x else x) = x := by
    split_ifs with hh
    · exact hUi z x (by rw [le_antisymm hx hh, abs_zero]; exact hε)
    · rfl
  have hGfixed (z : ℝ) (x : E × ℝ) (hx : x ∉ K) :
      G z x = x ∧ (G z).symm x = x := by
    have hFx := hfixed z x hx
    have hFix : (F z).symm x = x := by
      have hh := congrArg (F z).symm hFx
      simpa only [Diffeomorph.symm_apply_apply] using hh.symm
    change (if 0 ≤ x.2 then F z x else x) = x ∧
      (if 0 ≤ x.2 then (F z).symm x else x) = x
    simp only [hFx, hFix, ite_self, and_self]
  refine ⟨G, hf, hg, (fun _ _ hx => if_pos hx), hlower _ hstrip,
    (fun _ _ hx => if_pos hx), hlower _ hstripi, hGfixed, ?_⟩
  intro z
  exact ⟨HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hGfixed z x hx).1),
    HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hGfixed z x hx).2)⟩

end PoincareConjecture.M25.Topology3D
