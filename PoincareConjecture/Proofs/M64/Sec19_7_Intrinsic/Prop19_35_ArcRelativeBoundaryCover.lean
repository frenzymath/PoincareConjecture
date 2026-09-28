import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RelativeBoundaryCover













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_exists_arc_smooth_edge
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B))
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0) (hp : p ∈ Ioo A B)
    {C : Set AnnulusCoordinates} (hC : IsCompact C) (hpC : gamma p ∉ C) :
    ∃ (e : SmoothEdge AnnulusCoordinates) (W : Set AnnulusCoordinates),
      e.map (1 / 2) = gamma p ∧ InjOn e.map (Icc (0 : ℝ) 1) ∧
      e.map '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc A B ∧
      IsOpen W ∧ gamma p ∈ W ∧
      W ∩ (gamma '' Icc A B ∪ C) ⊆ e.map '' Icc (0 : ℝ) 1 := by
  let radius := min (p - A) (B - p) / 2
  have hr : 0 < radius := half_pos (lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))
  have hrA : radius < p - A :=
    (half_lt_self (lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))).trans_le (min_le_left _ _)
  have hrB : radius < B - p :=
    (half_lt_self (lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))).trans_le (min_le_right _ _)
  let a := p - radius
  let b := p + radius
  have ha : A < a := by dsimp only [a]; linarith
  have hb : b < B := by dsimp only [b]; linarith
  have hap : a < p := sub_lt_self p hr
  have hpb : p < b := lt_add_of_pos_right p hr
  have hab : a < b := hap.trans hpb
  let parameter : ℝ → ℝ := fun t => a + t * (b - a)
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : parameter t ∈ Icc a b := by
    dsimp only [parameter]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg ht.1 (sub_pos.mpr hab).le)
    · nlinarith [ht.2]
  have hparamI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : parameter t ∈ Ioo A B :=
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
  let tail := gamma '' (Icc A a ∪ Icc b B) ∪ C
  have htail : IsClosed tail :=
    (((isCompact_Icc.union isCompact_Icc).image hg.continuous).union hC).isClosed
  have hpnot : gamma p ∉ tail := by
    rintro (⟨t, ht, htp⟩ | hp')
    · have htI : t ∈ Icc A B := by
        rcases ht with ht | ht
        · exact ⟨ht.1, ht.2.trans (hab.le.trans hb.le)⟩
        · exact ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩
      have htp' := hinj htI (Ioo_subset_Icc_self hp) htp
      subst t
      rcases ht with ht | ht <;> linarith [ht.1, ht.2]
    · exact hpC hp'
  refine ⟨e, tailᶜ, by rw [heq, hhalf], ?_, ?_, htail.isOpen_compl, hpnot, ?_⟩
  · intro s hs t ht hst
    have h := hinj (Ioo_subset_Icc_self (hparamI s hs))
      (Ioo_subset_Icc_self (hparamI t ht)) hst
    dsimp [parameter] at h
    exact mul_right_cancel₀ (sub_pos.mpr hab).ne' (add_left_cancel h)
  · rw [himage]
    exact image_mono (Icc_subset_Icc ha.le hb.le)
  · rintro z ⟨hznot, (⟨t, ht, rfl⟩ | hzC)⟩
    · rw [himage]
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · by_contra hn
        exact hznot (Or.inl ⟨t, Or.inl ⟨ht.1, (lt_of_not_ge hn).le⟩, rfl⟩)
      · by_contra hn
        exact hznot (Or.inl ⟨t, Or.inr ⟨(lt_of_not_ge hn).le, ht.2⟩, rfl⟩)
    · exact False.elim (hznot (Or.inr hzC))




theorem m64Intrinsic_exists_arc_relative_cover_of_local_frontier
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B))
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0) (hp : p ∈ Ioo A B)
    {C : Set AnnulusCoordinates} (hC : IsCompact C) (hpC : gamma p ∉ C)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc A B ∪ C)
    (hfV : frontier V = gamma '' Icc A B ∪ C)
    {K : Set AnnulusCoordinates} (hK : IsClosed K)
    (hKregular : closure (interior K) = K) (hKsub : K ⊆ closure U)
    (hpK : gamma p ∈ K) {N : Set AnnulusCoordinates} (hN : N ∈ 𝓝 (gamma p))
    (hfrontK : N ∩ frontier K ⊆ gamma '' Icc A B ∪ C) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ K := by
  obtain ⟨e, O, he, hinje, hearc, hO, hpO, hOarc⟩ :=
    m64Intrinsic_exists_arc_smooth_edge hg hinj hregular hp hC hpC
  have hUregular := m64Intrinsic_jordan_interior_closure hU hV hdisj (hfU.trans hfV.symm)
  have hVregular := m64Intrinsic_jordan_interior_closure hV hU hdisj.symm (hfV.trans hfU.symm)
  have hthin : interior (e.map '' Icc (0 : ℝ) 1) = ∅ := by
    apply subset_empty_iff.mp
    rw [← interior_frontier (isClosed_closure : IsClosed (closure U))]
    apply interior_mono
    rw [hUregular.2, hfU]
    exact hearc.trans subset_union_left
  have hdisjoint : Disjoint (interior K) (interior (closure V)) := by
    rw [hVregular.1]
    apply hdisj.mono_left
    rw [← hUregular.1]
    exact interior_mono hKsub
  have hpV : gamma p ∈ closure V := by
    apply frontier_subset_closure
    rw [hfV]
    exact Or.inl ⟨p, Ioo_subset_Icc_self hp, rfl⟩
  have hneighborhood : N ∩ O ∈ 𝓝 (e.map (1 / 2)) := by
    rw [he]
    exact inter_mem hN (hO.mem_nhds hpO)
  have hpinterior : gamma p ∈ interior (K ∪ closure V) := by
    rw [← he]
    apply e.mem_interior_union_of_local_frontiers (0 : AnnulusCoordinates)
      hinje (by intro z _; simp) hthin hK isClosed_closure hKregular
      (by rw [hVregular.1]) hdisjoint (by norm_num)
      (he ▸ hpK) (he ▸ hpV) hneighborhood
    · intro z hz
      exact hOarc ⟨hz.1.2, hfrontK ⟨hz.1.1, hz.2⟩⟩
    · intro z hz
      apply hOarc
      refine ⟨hz.1.2, ?_⟩
      simpa only [hVregular.2, hfV] using hz.2
  refine ⟨interior (K ∪ closure V), isOpen_interior, hpinterior, ?_⟩
  intro z hz
  apply hK.closure_subset
  apply mem_closure_iff.mpr
  intro O hO hzO
  obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hz.2
    (O ∩ interior (K ∪ closure V)) (hO.inter isOpen_interior) ⟨hzO, hz.1⟩
  refine ⟨y, hy.1, ?_⟩
  rcases interior_subset hy.2 with hyK | hyV
  · exact hyK
  · exact False.elim (disjoint_left.mp (hdisj.closure_right hU) hyU hyV)

end PoincareConjecture
