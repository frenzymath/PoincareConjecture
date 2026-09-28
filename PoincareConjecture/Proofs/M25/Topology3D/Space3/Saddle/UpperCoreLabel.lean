import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCoreFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Function Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_upper_core_label
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (z : ℝ)
    (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = z}) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let Kz : Set UnitTwoSphere := D.sourceCore ∩ {q | z ≤ f q}
    ∃ i : Fin D.capCount,
      let C := D.cap i
      let ell := C.cutHeight - C.removal
      C.sign = -1 ∧ (∀ k : Fin D.capCount, (D.cap k).sign = -1 ↔ k = i) ∧
      z < ell ∧
      {q : UnitTwoSphere | f q ∈ Icc z ell} = Kz ∧
      {q : UnitTwoSphere | f q = ell} = C.sourceSeam ∧
      C.sourceCap ∪ Kz = {q : UnitTwoSphere | z ≤ f q} ∧
      ∀ q ∈ Kz, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := by
  classical
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  let Kz : Set UnitTwoSphere := D.sourceCore ∩ {q | z ≤ f q}
  let Lz : Set UnitTwoSphere := {q | f q = z}
  change c < z at hcz
  change ∀ i : Fin D.capCount, (D.cap i).sign = -1 → z < ell i at hseams
  change IsConnected Lz at hlevel
  have hf : Continuous f := continuous_const.inner
    (collar_central_contMDiff psi hpsi).continuous
  obtain ⟨P, U, hP, hU, hKU, hLK, hPzero, hPadd, hPderiv, htrack⟩ :=
    exists_saddle_upper_core_flow psi hpsi u D z hcz hseams
  change Kz ⊆ U at hKU
  change Lz ⊆ Kz at hLK
  change ∀ t q, P (t, q) ∈ U → HasDerivAt (fun s => f (P (s, q))) 1 t at hPderiv
  change ∀ q ∈ Kz, ∀ t ∈ Icc (0 : ℝ) (f q - z),
    P (-t, q) ∈ Kz ∧ f (P (-t, q)) = f q - t at htrack
  have hPc : Continuous P := hP.continuous
  have hPt (t : ℝ) : Continuous (fun q : UnitTwoSphere => P (t, q)) :=
    hPc.comp (continuous_const.prodMk continuous_id)
  have hPq (q : UnitTwoSphere) : Continuous (fun t : ℝ => P (t, q)) :=
    hPc.comp (continuous_id.prodMk continuous_const)
  have hsignSq (i : Fin D.capCount) : (D.cap i).sign * (D.cap i).sign = 1 := by
    rcases D.cut_side i with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;> norm_num
  have hsides (i : Fin D.capCount) :
      ((D.cap i).sign = 1 ∧ ell i < c) ∨
      ((D.cap i).sign = -1 ∧ c < ell i) := by
    have hrem := (D.removal_lt_cutRadius i).trans (D.cutRadius_lt_gap i)
    change (D.cap i).removal < |(D.cap i).cutHeight - c| at hrem
    rcases D.cut_side i with ⟨hi, hm⟩ | ⟨hi, hm⟩
    · change (D.cap i).cutHeight < c at hm
      rw [abs_of_neg (sub_neg.mpr hm)] at hrem
      refine Or.inl ⟨hi, ?_⟩
      dsimp only [ell]; rw [hi]; linarith
    · change c < (D.cap i).cutHeight at hm
      rw [abs_of_pos (sub_pos.mpr hm)] at hrem
      refine Or.inr ⟨hi, ?_⟩
      dsimp only [ell]; rw [hi]; linarith
  have hplacement (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 < (D.cap i).overlapWidth) :
      f ((D.cap i).sourceChart p) =
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2) := by
    have htp : (((D.cap i).profile.model p).1,
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2)) ∈
        (D.cap i).tube.source := (D.cap i).tube_source
      ⟨mem_closedBall_zero_iff.mpr ((D.cap i).profile.model_fst_norm_le p), mem_univ _⟩
    dsimp only [f]
    rw [(D.cap i).central_eq p hp, SurgeryCapProfile.capMap_apply]
    exact (D.cap i).tube_height _ htp
  have hscaled (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 ≤ 0) :
      (D.cap i).sign * (f ((D.cap i).sourceChart p) - ell i) =
        (D.cap i).scale * ((D.cap i).profile.model p).2 := by
    calc
      _ = ((D.cap i).sign * (D.cap i).sign) *
          ((D.cap i).scale * ((D.cap i).profile.model p).2) := by
        rw [hplacement i p (hp.trans_lt (D.cap i).overlap_pos)]
        dsimp only [ell]
        ring
      _ = _ := by rw [hsignSq i, one_mul]
  have hcapHeight (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceCap) : (D.cap i).sign * (f q - ell i) ≤ 0 := by
    obtain ⟨p, hp, rfl⟩ := hq
    have hm : ((D.cap i).profile.model p).2 ≤ 0 :=
      (surgeryCapModel_snd_nonpos_iff _ _ _ _ _ _ (D.cap i).profile.vertical_pos p).mpr hp
    rw [hscaled i p hp]
    exact mul_nonpos_of_nonneg_of_nonpos (D.cap i).scale_pos.le hm
  have hseamHeight (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceSeam) : f q = ell i := by
    obtain ⟨p, hp, rfl⟩ := hq
    have hm : ((D.cap i).profile.model p).2 = 0 := by
      have hh := surgeryCapModel_cylinder
        (D.cap i).profile.horizontal (D.cap i).profile.vertical
        (D.cap i).profile.horizontal_smooth (D.cap i).profile.vertical_smooth
        (fun x => ((D.cap i).profile.horizontal_pos x).ne')
        (fun x => ((D.cap i).profile.vertical_pos x).ne')
        (D.cap i).profile.horizontal_near (D.cap i).profile.vertical_far p
        (by rw [hp]; norm_num)
      exact (congrArg Prod.snd hh).trans hp
    rw [hplacement i p (by rw [hp]; exact (D.cap i).overlap_pos), hm]
    dsimp only [ell]
    ring
  have hcapAtSeam (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceCap) (hh : f q = ell i) :
      q ∈ (D.cap i).sourceSeam := by
    obtain ⟨p, hp, rfl⟩ := hq
    have hzero := hscaled i p hp
    rw [hh, sub_self, mul_zero] at hzero
    have hnative : (heightCoordinates (p : E3)).2 = 0 := by
      apply le_antisymm hp
      by_contra hn
      have hm : ((D.cap i).profile.model p).2 < 0 :=
        (surgeryCapModel_snd_neg_iff _ _ _ _ _ _ (D.cap i).profile.vertical_pos p).mpr
          (lt_of_not_ge hn)
      have hc := mul_neg_of_pos_of_neg (D.cap i).scale_pos hm
      linarith
    exact ⟨p, hnative, rfl⟩
  have hseamCap (i : Fin D.capCount) : (D.cap i).sourceSeam ⊆ (D.cap i).sourceCap := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨p, hp.le, rfl⟩
  have hseamCore (i : Fin D.capCount) : (D.cap i).sourceSeam ⊆ D.sourceCore := by
    intro q hq
    have hh : q ∈ D.sourceCore ∩ (D.cap i).sourceCap := by
      rw [D.source_incidence i]
      exact hq
    exact hh.1
  have hseamK (i : Fin D.capCount) (hi : (D.cap i).sign = -1) :
      (D.cap i).sourceSeam ⊆ Kz := by
    intro q hq
    refine ⟨hseamCore i hq, ?_⟩
    change z ≤ f q
    rw [hseamHeight i q hq]
    exact (hseams i hi).le
  have hregular (q : UnitTwoSphere) (hq : q ∈ Kz) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := by
    intro hh
    have hp := (D.unique_critical q hq.1).mp hh
    have hzq : z ≤ f q := hq.2
    rw [hp] at hzq
    exact (not_le_of_gt hcz) hzq
  have hhalf (i : Fin D.capCount) (hi : (D.cap i).sign = -1) :
      ∃ O : Set UnitTwoSphere, IsOpen O ∧ (D.cap i).sourceSeam ⊆ O ∧
        O ∩ {q | f q = ell i} = (D.cap i).sourceSeam ∧
        D.sourceCore ∩ O ⊆ {q | f q ≤ ell i} := by
    let C := D.cap i
    let d := min (C.overlapWidth / 2) (1 / 8)
    have hd : 0 < d := lt_min (half_pos C.overlap_pos) (by norm_num)
    have hdO : d < C.overlapWidth := (min_le_left _ _).trans_lt (by linarith [C.overlap_pos])
    have hdQ : d < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
    let V : Set UnitTwoSphere := {p | |(heightCoordinates (p : E3)).2| < d}
    have hVc : Continuous (fun p : UnitTwoSphere => |(heightCoordinates (p : E3)).2|) :=
      ((heightCoordinates.continuous.comp continuous_subtype_val).snd).abs
    have hVo : IsOpen V := isOpen_lt hVc continuous_const
    have hVs : V ⊆ C.sourceChart.source := by
      intro p hp
      exact C.source_band p ((le_abs_self _).trans_lt (hp.trans hdO))
    let O := C.sourceChart '' V
    have hOo : IsOpen O := C.sourceChart.isOpen_image_of_subset_source hVo hVs
    have hSO : C.sourceSeam ⊆ O := by
      rintro q ⟨p, hp, rfl⟩
      exact ⟨p, by change |(heightCoordinates (p : E3)).2| < d; rw [hp, abs_zero]; exact hd, rfl⟩
    have hvheight (p : UnitTwoSphere) (hp : p ∈ V) :
        f (C.sourceChart p) = ell i - C.scale * (heightCoordinates (p : E3)).2 := by
      have hm := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun x => (C.profile.horizontal_pos x).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far p (hp.le.trans hdQ.le)
      have hheight : (C.profile.model p).2 = (heightCoordinates (p : E3)).2 := by
        have hh := congrArg (fun x : E2 × ℝ => x.2) hm
        exact hh
      rw [hplacement i p ((le_abs_self _).trans_lt (hp.trans hdO)), hheight]
      dsimp only [ell]
      rw [hi]
      ring
    have hlevelO : O ∩ {q | f q = ell i} = C.sourceSeam := by
      ext q
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hq⟩
        refine ⟨p, ?_, rfl⟩
        change (heightCoordinates (p : E3)).2 = 0
        have hh := hvheight p hp
        change f (C.sourceChart p) = ell i at hq
        have hz : C.scale * (heightCoordinates (p : E3)).2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left C.scale_pos.ne'
      · intro hq
        exact ⟨hSO hq, hseamHeight i q hq⟩
    refine ⟨O, hOo, hSO, hlevelO, ?_⟩
    rintro q ⟨hqK, p, hp, rfl⟩
    change f (C.sourceChart p) ≤ ell i
    by_contra hh
    have hv : (heightCoordinates (p : E3)).2 < 0 := by
      have hph := hvheight p hp
      apply (mul_lt_mul_iff_right₀ C.scale_pos).mp
      linarith
    have hcap : C.sourceChart p ∈ C.sourceCap := ⟨p, hv.le, rfl⟩
    have hs : C.sourceChart p ∈ C.sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hqK, hcap⟩
    exact hh (hseamHeight i _ hs).le
  have hheight (q : UnitTwoSphere) (T : ℝ) (hT : 0 ≤ T)
      (hstay : ∀ t ∈ Icc (0 : ℝ) T, P (t, q) ∈ U) :
      f (P (T, q)) = f q + T := by
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        HasDerivAt (fun s : ℝ => f (P (s, q)) - s) 0 t := by
      have hh : HasDerivAt (fun s : ℝ => f (P (s, q)) - s) ((1 : ℝ) - 1) t :=
        (hPderiv t q (hstay t ht)).sub (hasDerivAt_id t)
      simpa only [sub_self] using hh
    have hh : ‖(f (P (T, q)) - T) - (f (P (0, q)) - 0)‖ ≤ 0 := by
      have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht => (hd t ht).hasDerivWithinAt)
        (fun _ _ => show ‖(0 : ℝ)‖ ≤ 0 by simp) (convex_Icc (0 : ℝ) T)
        (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
        (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
      simpa only [zero_mul] using hn
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp hh)
    rw [hPzero, sub_zero] at heq
    linarith
  have hincrease (q : UnitTwoSphere) (hq : q ∈ U) (V : Set UnitTwoSphere)
      (hV : IsOpen V) (hqV : q ∈ V) :
      ∃ t : ℝ, 0 < t ∧ P (t, q) ∈ V ∧ f (P (t, q)) = f q + t := by
    have h0 : P (0, q) ∈ U ∩ V := by rw [hPzero]; exact ⟨hq, hqV⟩
    have hn := (hPq q).continuousAt.eventually ((hU.inter hV).mem_nhds h0)
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
    have hstay (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (d / 2)) : P (s, q) ∈ U ∩ V := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [hs.2]
    exact ⟨d / 2, by positivity, (hstay _ ⟨by positivity, le_rfl⟩).2,
      hheight q (d / 2) (by positivity) (fun s hs => (hstay s hs).1)⟩
  let A : Fin D.capCount → Set UnitTwoSphere := fun i =>
    (fun q => P (z - ell i, q)) '' (D.cap i).sourceSeam
  have hAcompact (i : Fin D.capCount) : IsCompact (A i) :=
    (D.cap i).sourceSeam_isCompact.image (hPt (z - ell i))
  have hAnonempty (i : Fin D.capCount) : (A i).Nonempty :=
    (D.cap i).sourceSeam_isConnected.nonempty.image _
  have hAL (i : Fin D.capCount) (hi : (D.cap i).sign = -1) : A i ⊆ Lz := by
    rintro x ⟨q, hq, rfl⟩
    have hqH := hseamHeight i q hq
    have hh := (htrack q (hseamK i hi hq) (ell i - z)
      ⟨sub_nonneg.mpr (hseams i hi).le, by rw [hqH]⟩).2
    change f (P (z - ell i, q)) = z
    have htime : -(ell i - z) = z - ell i := by ring
    rw [htime, hqH] at hh
    linarith
  have hAopen (i : Fin D.capCount) (hi : (D.cap i).sign = -1) :
      ∀ x ∈ A i, ∃ V : Set UnitTwoSphere,
        IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ Lz → y ∈ A i := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hx
    obtain ⟨O, hOo, hSO, hOlevel, _hOside⟩ := hhalf i hi
    let T := ell i - z
    have hT : 0 < T := sub_pos.mpr (hseams i hi)
    have hback (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P (t, x) ∈ U := by
      have htq : T - t ∈ Icc (0 : ℝ) (f q - z) := by
        rw [hseamHeight i q hq]
        dsimp only [T] at ht ⊢
        constructor <;> linarith [ht.1, ht.2]
      have hqt := hKU (htrack q (hseamK i hi hq) (T - t) htq).1
      have heq : P (t, x) = P (-(T - t), q) := by
        rw [← hqx, hPadd]
        congr 1
        dsimp [T]
        ring
      rw [heq]
      exact hqt
    have hEnd : P (T, x) = q := by
      rw [← hqx, hPadd]
      have ht : T + (z - ell i) = 0 := by dsimp [T]; ring
      rw [ht, hPzero]
    obtain ⟨J, V, _hJo, hVo, hIJ, hxV, hprod⟩ := generalized_tube_lemma
      (s := Icc (0 : ℝ) T) isCompact_Icc (t := {x}) isCompact_singleton
      (hU.preimage hPc) (by
        rintro ⟨t, y⟩ ⟨ht, hy⟩
        change P (t, y) ∈ U
        change y = x at hy
        rw [hy]
        exact hback t ht)
    let V' := V ∩ (fun y : UnitTwoSphere => P (T, y)) ⁻¹' O
    refine ⟨V', hVo.inter (hOo.preimage (hPt T)), ?_, ?_⟩
    · exact ⟨hxV (mem_singleton x), by change P (T, x) ∈ O; rw [hEnd]; exact hSO hq⟩
    · intro y hy hyL
      have hstay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P (t, y) ∈ U :=
        hprod ⟨hIJ ht, hy.1⟩
      have hyEnd : P (T, y) ∈ (D.cap i).sourceSeam := by
        rw [← hOlevel]
        refine ⟨hy.2, ?_⟩
        change f (P (T, y)) = ell i
        rw [hheight y T hT.le hstay]
        change f y = z at hyL
        rw [hyL]
        dsimp [T]
        ring
      refine ⟨P (T, y), hyEnd, ?_⟩
      change P (z - ell i, P (T, y)) = y
      rw [hPadd]
      have ht : z - ell i + T = 0 := by dsimp [T]; ring
      rw [ht, hPzero]
  have hAeq (i : Fin D.capCount) (hi : (D.cap i).sign = -1) : A i = Lz := by
    choose V hVo hxV hVsub using hAopen i hi
    let O := ⋃ x : A i, V x.1 x.2
    have hOo : IsOpen O := isOpen_iUnion (fun x : A i => hVo x.1 x.2)
    have hAO : A i ⊆ O := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    have hOL : O ∩ Lz ⊆ A i := by
      rintro x ⟨hx, hxL⟩
      obtain ⟨y, hy⟩ := mem_iUnion.mp hx
      exact hVsub y.1 y.2 x hy hxL
    apply Subset.antisymm (hAL i hi)
    intro x hxL
    by_contra hxA
    obtain ⟨a, ha⟩ := hAnonempty i
    have hcover : Lz ⊆ O ∪ (A i)ᶜ := by
      intro y _
      by_cases hy : y ∈ A i
      · exact Or.inl (hAO hy)
      · exact Or.inr hy
    obtain ⟨y, hy⟩ := hlevel.isPreconnected O (A i)ᶜ hOo
      (hAcompact i).isClosed.isOpen_compl hcover
      ⟨a, hAL i hi ha, hAO ha⟩ ⟨x, hxL, hxA⟩
    exact hy.2.2 (hOL ⟨hy.2.1, hy.1⟩)
  have hmatching (i k : Fin D.capCount) (hi : (D.cap i).sign = -1)
      (hk : (D.cap k).sign = -1) :
      ∃ p ∈ (D.cap i).sourceSeam, ∃ q ∈ (D.cap k).sourceSeam,
        p = P (ell i - ell k, q) := by
    obtain ⟨x, hx⟩ := hlevel.nonempty
    obtain ⟨p, hp, hpx⟩ : x ∈ A i := by rw [hAeq i hi]; exact hx
    obtain ⟨q, hq, hqx⟩ : x ∈ A k := by rw [hAeq k hk]; exact hx
    change P (z - ell i, p) = x at hpx
    change P (z - ell k, q) = x at hqx
    refine ⟨p, hp, q, hq, ?_⟩
    calc
      p = P (ell i - z, P (z - ell i, p)) := by
        rw [hPadd]
        have ht : ell i - z + (z - ell i) = 0 := by ring
        rw [ht, hPzero]
      _ = P (ell i - z, P (z - ell k, q)) := by rw [hpx, hqx]
      _ = P (ell i - ell k, q) := by rw [hPadd]; congr 1; ring
  have hnoLess (i k : Fin D.capCount) (hi : (D.cap i).sign = -1)
      (hk : (D.cap k).sign = -1) (hik : ell i < ell k) : False := by
    obtain ⟨p, hp, q, hq, hpq⟩ := hmatching i k hi hk
    obtain ⟨O, hOo, hSO, _hOL, hside⟩ := hhalf i hi
    let t0 := ell k - ell i
    have ht0 : 0 < t0 := sub_pos.mpr hik
    have htT : t0 < ell k - z := by dsimp [t0]; linarith [hseams i hi]
    let gamma : ℝ → UnitTwoSphere := fun t => P (-t, q)
    have hgc : Continuous gamma := hPc.comp (continuous_id.neg.prodMk continuous_const)
    have hgp : gamma t0 = p := by
      change P (-t0, q) = p
      rw [hpq]
      congr 1
      dsimp [t0]
      ring
    have hgpO : gamma t0 ∈ O := by rw [hgp]; exact hSO hp
    have hn : ∀ᶠ t : ℝ in 𝓝 t0, gamma t ∈ O :=
      hgc.continuousAt.eventually (hOo.mem_nhds hgpO)
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
    let e := min (d / 2) (t0 / 2)
    have he : 0 < e := lt_min (by positivity) (by positivity)
    have hed : e < d := (min_le_left _ _).trans_lt (by linarith)
    have het : e ≤ t0 / 2 := min_le_right _ _
    have hs : t0 - e ∈ Icc (0 : ℝ) (f q - z) := by
      rw [hseamHeight k q hq]
      constructor <;> linarith
    have hqstep := htrack q (hseamK k hk hq) (t0 - e) hs
    have hOstep : gamma (t0 - e) ∈ O := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have hh : t0 - e - t0 = -e := by ring
      rw [hh, abs_neg, abs_of_pos he]
      exact hed
    have hbound : f (gamma (t0 - e)) ≤ ell i := hside ⟨hqstep.1.1, hOstep⟩
    have hheightStep := hqstep.2
    rw [hseamHeight k q hq] at hheightStep
    change f (gamma (t0 - e)) = ell k - (t0 - e) at hheightStep
    dsimp only [t0] at hheightStep
    linarith
  have honly (i k : Fin D.capCount) (hi : (D.cap i).sign = -1)
      (hk : (D.cap k).sign = -1) : i = k := by
    rcases lt_trichotomy (ell i) (ell k) with hlt | heq | hgt
    · exact False.elim (hnoLess i k hi hk hlt)
    · by_contra hik
      obtain ⟨p, hp, q, hq, hpq⟩ := hmatching i k hi hk
      rw [heq, sub_self, hPzero] at hpq
      exact disjoint_left.mp (D.sourceCap_disjoint i k hik)
        (hseamCap i hp) (hpq.symm ▸ hseamCap k hq)
    · exact False.elim (hnoLess k i hk hi hgt)
  have hKcompact : IsCompact Kz :=
    D.sourceCore_compact.inter_right (isClosed_le continuous_const hf)
  have hKnonempty : Kz.Nonempty := hlevel.nonempty.mono hLK
  let Caps : Set UnitTwoSphere := ⋃ i : Fin D.capCount, (D.cap i).sourceCap
  have hCaps : IsCompact Caps := isCompact_iUnion (fun i => (D.cap i).sourceCap_isCompact)
  have hcover (q : UnitTwoSphere) : q ∈ D.sourceCore ∪ Caps := by
    change q ∈ D.sourceCore ∪ ⋃ i : Fin D.capCount, (D.cap i).sourceCap
    rw [D.source_cover]
    exact mem_univ _
  have houtside : Capsᶜ ⊆ D.sourceCore := by
    intro q hq
    have hc := hcover q
    rcases hc with hc | hc
    · exact hc
    · exact False.elim (hq hc)
  have hmaxSeam (q : UnitTwoSphere) (hq : q ∈ Kz) (hm : IsMaxOn f Kz q) :
      ∃ i : Fin D.capCount, q ∈ (D.cap i).sourceSeam ∧ (D.cap i).sign = -1 := by
    have hqC : q ∈ Caps := by
      by_contra hqC
      obtain ⟨t, ht, hpC, hpH⟩ := hincrease q (hKU hq) Capsᶜ
        hCaps.isClosed.isOpen_compl hqC
      have hpK : P (t, q) ∈ Kz := by
        refine ⟨houtside hpC, ?_⟩
        change z ≤ f (P (t, q))
        rw [hpH]
        exact hq.2.trans (le_add_of_nonneg_right ht.le)
      have hh : f (P (t, q)) ≤ f q := hm hpK
      rw [hpH] at hh
      linarith
    obtain ⟨i, hi⟩ := mem_iUnion.mp hqC
    have hqs : q ∈ (D.cap i).sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hq.1, hi⟩
    refine ⟨i, hqs, ?_⟩
    have hh := hseamHeight i q hqs
    rcases hsides i with ⟨_, hlow⟩ | ⟨hs, _⟩
    · have hzq : z ≤ f q := hq.2
      linarith
    · exact hs
  obtain ⟨qmax, hqmax, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty hf.continuousOn
  obtain ⟨i, hmaxSeamI, hi⟩ := hmaxSeam qmax hqmax hmax
  have hbound (q : UnitTwoSphere) (hq : q ∈ Kz) : f q ≤ ell i :=
    (hmax hq).trans_eq (hseamHeight i qmax hmaxSeamI)
  have hKtop (q : UnitTwoSphere) (hq : q ∈ Kz) (hh : f q = ell i) :
      q ∈ (D.cap i).sourceSeam := by
    have hm : IsMaxOn f Kz q := fun x hx => (hbound x hx).trans_eq hh.symm
    obtain ⟨k, hqk, hk⟩ := hmaxSeam q hq hm
    rwa [honly k i hk hi] at hqk
  have hlevelEll : {q : UnitTwoSphere | f q = ell i} = (D.cap i).sourceSeam := by
    ext q
    constructor
    · intro hq
      change f q = ell i at hq
      have hc := hcover q
      rcases hc with hc | hc
      · exact hKtop q ⟨hc, by change z ≤ f q; rw [hq]; exact (hseams i hi).le⟩ hq
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hc
        have hcap := hcapHeight k q hk
        rcases hsides k with ⟨hks, hlow⟩ | ⟨hks, _⟩
        · rw [hks, one_mul, hq] at hcap
          linarith [hseams i hi]
        · have hki := honly k i hks hi
          subst k
          exact hcapAtSeam i q hk hq
    · exact hseamHeight i q
  have hband : {q : UnitTwoSphere | f q ∈ Icc z (ell i)} = Kz := by
    ext q
    constructor
    · intro hq
      have hc := hcover q
      rcases hc with hc | hc
      · exact ⟨hc, hq.1⟩
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hc
        have hcap := hcapHeight k q hk
        rcases hsides k with ⟨hks, hlow⟩ | ⟨hks, _⟩
        · rw [hks, one_mul] at hcap
          exfalso
          linarith [hq.1]
        · have hki := honly k i hks hi
          subst k
          rw [hi] at hcap
          have hh : f q = ell i := by nlinarith [hq.2]
          exact ⟨hseamCore i (hcapAtSeam i q hk hh), hq.1⟩
    · intro hq
      exact ⟨hq.2, hbound q hq⟩
  have hsuper : (D.cap i).sourceCap ∪ Kz = {q : UnitTwoSphere | z ≤ f q} := by
    ext q
    constructor
    · rintro (hq | hq)
      · have hh := hcapHeight i q hq
        rw [hi] at hh
        change z ≤ f q
        nlinarith [hseams i hi]
      · exact hq.2
    · intro hq
      change z ≤ f q at hq
      have hc := hcover q
      rcases hc with hc | hc
      · exact Or.inr ⟨hc, hq⟩
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hc
        have hcap := hcapHeight k q hk
        rcases hsides k with ⟨hks, hlow⟩ | ⟨hks, _⟩
        · rw [hks, one_mul] at hcap
          exfalso
          linarith
        · exact Or.inl (honly k i hks hi ▸ hk)
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_, hregular⟩
  · intro k
    exact ⟨fun hk => honly k i hk hi, fun hk => hk.symm ▸ hi⟩
  · simpa only [ell, hi, neg_one_mul, sub_eq_add_neg] using hseams i hi
  · simpa only [ell, hi, neg_one_mul, sub_eq_add_neg] using hband
  · simpa only [ell, hi, neg_one_mul, sub_eq_add_neg] using hlevelEll
  · exact hsuper

end PoincareConjecture.M25.Topology3D
