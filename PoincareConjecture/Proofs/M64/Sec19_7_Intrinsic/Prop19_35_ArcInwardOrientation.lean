import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcNormalNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopInwardCollar

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem signed_arc_strip_of_point
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {a b delta sigma p : ℝ} (_hdelta : 0 < delta)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hsource : Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source)
    (hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0)
    (hp : p ∈ Icc a b)
    (hpoint : ∃ r ∈ Ioo (0 : ℝ) delta, H (p, sigma * r) ∈ U) :
    ∀ t ∈ Icc a b, ∀ r ∈ Ioo (0 : ℝ) delta, H (t, sigma * r) ∈ U := by
  let S := Icc a b ×ˢ Ioo (0 : ℝ) delta
  let F : ℝ × ℝ → AnnulusCoordinates := fun q => H (q.1, sigma * q.2)
  have habs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have hsne : sigma ≠ 0 := by rcases hsigma with rfl | rfl <;> norm_num
  have hS (q : ℝ × ℝ) (hq : q ∈ S) : (q.1, sigma * q.2) ∈ H.source := by
    apply hsource
    refine ⟨hq.1, abs_lt.mp ?_⟩
    rw [abs_mul, habs, one_mul, abs_of_pos hq.2.1]
    exact hq.2.2
  have hconn : IsPreconnected (F '' S) :=
    (isPreconnected_Icc.prod isPreconnected_Ioo).image F
      (H.continuousOn.comp
        (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn hS)
  obtain ⟨r, hr, hrU⟩ := hpoint
  have hsub : F '' S ⊆ U := hconn.subset_of_closure_inter_subset hU
    ⟨F (p, r), ⟨(p, r), ⟨hp, hr⟩, rfl⟩, hrU⟩ (by
      rintro z ⟨hz, q, hq, rfl⟩
      by_contra hn
      have hf : F q ∈ frontier U := ⟨hz, by simpa only [hU.interior_eq] using hn⟩
      exact (mul_ne_zero hsne hq.2.1.ne') ((hfront _ (hS q hq)).mp hf))
  exact fun t ht r hr => hsub ⟨(t, r), ⟨ht, hr⟩, rfl⟩

theorem m64Intrinsic_exists_global_arc_inward_sign
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B : ℝ}
    (hAB : A < B) (hinj : InjOn gamma (Icc A B))
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo A B, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U) :
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ t ∈ Ioo A B, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        gamma t + r • (sigma • quarterTurn (deriv gamma t)) ∈ U := by
  let p := (A + B) / 2
  have hp : p ∈ Ioo A B := ⟨by dsimp only [p]; linarith, by dsimp only [p]; linarith⟩
  obtain ⟨delta, hdelta, H, hsource, hmap, _, _, hline⟩ :=
    m64Intrinsic_exists_arc_normal_neighborhood hg hinj le_rfl hp.1 hp.2 hregular hK
      (fun t ht => havoid t (by have he : t = p := le_antisymm ht.2 ht.1; simpa only [he] using hp))
  have hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfU] using hline
  obtain ⟨sigma, hsigma, hinward⟩ := m64Intrinsic_normal_strip_occupied_side
    hU hV hdisj hfV.symm H le_rfl hdelta hsource hfront
  have hray : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma p + r • (sigma • quarterTurn (deriv gamma p)) ∈ U := by
    filter_upwards [Ioo_mem_nhdsGT hdelta] with r hr
    simpa only [hmap, normalStrip, smul_smul, mul_comm] using hinward p (by simp) r hr
  refine ⟨sigma, hsigma, ?_⟩
  intro t ht
  have ha : A < min p t := lt_min hp.1 ht.1
  have hb : max p t < B := max_lt hp.2 ht.2
  obtain ⟨rho, hrho, J, hJs, hJmap, _, _, hJline⟩ :=
    m64Intrinsic_exists_arc_normal_neighborhood hg hinj min_le_max ha hb hregular hK
      (fun s hs => havoid s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩)
  have hJfront : ∀ q ∈ J.source, J q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfU] using hJline
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) rho := Ioo_mem_nhdsGT hrho
  obtain ⟨r, hr, hrU⟩ := (hsmall.and hray).exists
  have hpoint : ∃ r ∈ Ioo (0 : ℝ) rho, J (p, sigma * r) ∈ U :=
    ⟨r, hr, by simpa only [hJmap, normalStrip, smul_smul, mul_comm] using hrU⟩
  have hinside := signed_arc_strip_of_point hU J hrho hsigma hJs hJfront
    (show p ∈ Icc (min p t) (max p t) from ⟨min_le_left _ _, le_max_left _ _⟩) hpoint
  filter_upwards [Ioo_mem_nhdsGT hrho] with r hr
  simpa only [hJmap, normalStrip, smul_smul, mul_comm] using
    hinside t ⟨min_le_right _ _, le_max_right _ _⟩ r hr

theorem m64Intrinsic_exists_global_arc_inward_orientation
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hT : 0 < T) (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U) :
    ∃ g : ℝ → AnnulusCoordinates,
      (g = gamma ∨ g = fun t => gamma (T - t)) ∧ ContDiff ℝ ∞ g ∧
      InjOn g (Icc 0 T) ∧ g '' Icc 0 T = gamma '' Icc 0 T ∧
      (∀ t ∈ Ioo (0 : ℝ) T, deriv g t ≠ 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, g t ∉ K) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g t + r • quarterTurn (deriv g t) ∈ U := by
  obtain ⟨sigma, hsigma, hray⟩ := m64Intrinsic_exists_global_arc_inward_sign
    hg hT hinj hregular hK havoid hU hV hdisj hfU hfV
  rcases hsigma with rfl | rfl
  · refine ⟨gamma, Or.inl rfl, hg, hinj, rfl, hregular, havoid, ?_⟩
    simpa only [one_smul] using hray
  · let g : ℝ → AnnulusCoordinates := fun t => gamma (T - t)
    have hg' : ContDiff ℝ ∞ g := hg.comp (contDiff_const.sub contDiff_id)
    have hi' : InjOn g (Icc (0 : ℝ) T) := by
      intro s hs t ht heq
      have he := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
    have himage : g '' Icc 0 T = gamma '' Icc 0 T := by
      change (gamma ∘ fun t => T - t) '' Icc 0 T = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
    have ht' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : T - t ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨g, Or.inr rfl, hg', hi', himage, ?_, fun t ht => havoid _ (ht' t ht), ?_⟩
    · intro t ht
      change deriv (fun s => gamma (T - s)) t ≠ 0
      rw [deriv_comp_const_sub]
      exact neg_ne_zero.mpr (hregular _ (ht' t ht))
    · intro t ht
      simpa only [g, deriv_comp_const_sub, map_neg, neg_one_smul] using hray _ (ht' t ht)

end PoincareConjecture
