import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_smooth_edge
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hp : p ∈ Ioo (0 : ℝ) T) :
    ∃ (e : SmoothEdge AnnulusCoordinates) (W : Set AnnulusCoordinates),
      e.map (1 / 2) = gamma p ∧ InjOn e.map (Icc (0 : ℝ) 1) ∧
      e.map '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc 0 T ∧
      IsOpen W ∧ gamma p ∈ W ∧
      W ∩ gamma '' Icc 0 T ⊆ e.map '' Icc (0 : ℝ) 1 := by
  let radius := min p (T - p) / 2
  have hr : 0 < radius := half_pos (lt_min hp.1 (sub_pos.mpr hp.2))
  have hrp : radius < p :=
    (half_lt_self (lt_min hp.1 (sub_pos.mpr hp.2))).trans_le (min_le_left _ _)
  have hrT : radius < T - p :=
    (half_lt_self (lt_min hp.1 (sub_pos.mpr hp.2))).trans_le (min_le_right _ _)
  let a := p - radius
  let b := p + radius
  have ha : 0 < a := sub_pos.mpr hrp
  have hb : b < T := by dsimp [b]; linarith
  have hap : a < p := sub_lt_self p hr
  have hpb : p < b := lt_add_of_pos_right p hr
  have hab : a < b := hap.trans hpb
  let parameter : ℝ → ℝ := fun t => a + t * (b - a)
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : parameter t ∈ Icc a b := by
    constructor
    · dsimp [parameter]
      exact le_add_of_nonneg_right (mul_nonneg ht.1 (sub_pos.mpr hab).le)
    · have hmul := mul_le_mul_of_nonneg_right ht.2 (sub_pos.mpr hab).le
      dsimp [parameter]
      linarith
  have hparamI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : parameter t ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans_le (hparameter t ht).1, (hparameter t ht).2.trans_lt hb⟩
  have hparamDeriv (t : ℝ) : HasDerivAt parameter (b - a) t := by
    convert! ((hasDerivAt_id t).mul_const (b - a)).const_add a using 1
    simp
  have hderiv (t : ℝ) : HasDerivAt (gamma ∘ parameter)
      ((b - a) • deriv gamma (parameter t)) t :=
    ((hg.differentiable (by simp)) (parameter t)).hasDerivAt.scomp t (hparamDeriv t)
  let e : SmoothEdge AnnulusCoordinates := {
    map := gamma ∘ parameter
    smooth := (hg.comp (by dsimp [parameter]; fun_prop)).contMDiff.contMDiffOn
    regular := by
      intro t ht
      rw [mfderiv_eq_fderiv, (hderiv t).hasFDerivAt.fderiv]
      have hne : (b - a) • deriv gamma (parameter t) ≠ 0 :=
        smul_ne_zero (sub_pos.mpr hab).ne' (hregular _ (hparamI t (Ioo_subset_Icc_self ht)))
      exact smul_left_injective ℝ hne }
  have heq (s : ℝ) : e.map s = gamma (parameter s) := rfl
  have hhalf : parameter (1 / 2) = p := by dsimp [parameter, a, b]; ring
  have himage : e.map '' Icc (0 : ℝ) 1 = gamma '' Icc a b := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨parameter t, hparameter t ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t - a) / (b - a),
        ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
          (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 a)⟩, ?_⟩
      rw [heq]
      congr 1
      dsimp [parameter]
      rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne', add_sub_cancel]
  let tail := gamma '' (Icc (0 : ℝ) a ∪ Icc b T)
  have htail : IsClosed tail :=
    ((isCompact_Icc.union isCompact_Icc).image hg.continuous).isClosed
  have hpnot : gamma p ∉ tail := by
    rintro ⟨t, ht, htp⟩
    have htI : t ∈ Icc (0 : ℝ) T := by
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans (hab.le.trans hb.le)⟩
      · exact ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩
    have htT : t < T := by
      by_contra hn
      have ht' : t = T := le_antisymm htI.2 (le_of_not_gt hn)
      have h0p := hinj ⟨le_rfl, hp.1.trans hp.2⟩ ⟨hp.1.le, hp.2⟩
        (hend.trans (ht' ▸ htp))
      linarith [hp.1]
    have htp' := hinj ⟨htI.1, htT⟩ ⟨hp.1.le, hp.2⟩ htp
    subst t
    rcases ht with ht | ht <;> linarith [ht.1, ht.2]
  refine ⟨e, tailᶜ, by rw [heq, hhalf], ?_, ?_, htail.isOpen_compl, hpnot, ?_⟩
  · intro s hs t ht hst
    have h := hinj
      ⟨(hparamI s hs).1.le, (hparamI s hs).2⟩
      ⟨(hparamI t ht).1.le, (hparamI t ht).2⟩ hst
    dsimp [parameter] at h
    exact mul_right_cancel₀ (sub_pos.mpr hab).ne' (add_left_cancel h)
  · rw [himage]
    exact image_mono (fun _ ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩)
  · rintro z ⟨hznot, t, ht, rfl⟩
    rw [himage]
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · by_contra hn
      exact hznot ⟨t, Or.inl ⟨ht.1, (lt_of_not_ge hn).le⟩, rfl⟩
    · by_contra hn
      exact hznot ⟨t, Or.inr ⟨(lt_of_not_ge hn).le, ht.2⟩, rfl⟩

end PoincareConjecture
