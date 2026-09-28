import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CoreTruncationRetraction
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Function Metric
open scoped ContDiff Manifold InnerProductSpace NNReal Topology Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_selected_wall_no_bypass
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hdeltaR : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target)
    (hcore : ∀ q : UnitTwoSphere,
      |⟪(u : E3), psi (q, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → q ∈ D.sourceCore)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let f : UnitTwoSphere → ℝ :=
      fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let c : ℝ := f D.point
    let rho : ℝ := 5 * R / 8
    let Dc : Set UnitTwoSphere :=
      D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let La : Set UnitTwoSphere := {q | f q = c - delta}
    ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅ := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  let rho : ℝ := 5 * R / 8
  let V : Set UnitTwoSphere :=
    D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
  let C0 : Set UnitTwoSphere :=
    D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
  let La : Set UnitTwoSphere := {q | f q = c - delta}
  let Lb : Set UnitTwoSphere := {q | f q = c + delta}
  let Km : Set UnitTwoSphere := D.sourceCore ∩ {q | f q ≤ c - delta}
  let Kp : Set UnitTwoSphere := D.sourceCore ∩ {q | c + delta ≤ f q}
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  change ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
    IsCompact (La \ B) → Disjoint B C0 → B = ∅
  have hj := collar_central_contMDiff psi hpsi
  have hf : Continuous f := H.continuous.comp hj.continuous
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hsides (i : Fin D.capCount) :
      ((D.cap i).sign = 1 ∧ ell i < c) ∨
      ((D.cap i).sign = -1 ∧ c < ell i) := by
    have hr := (D.removal_lt_cutRadius i).trans (D.cutRadius_lt_gap i)
    change (D.cap i).removal < |(D.cap i).cutHeight - c| at hr
    rcases D.cut_side i with ⟨hi, hm⟩ | ⟨hi, hm⟩
    · change (D.cap i).cutHeight < c at hm
      rw [abs_of_neg (sub_neg.mpr hm)] at hr
      refine Or.inl ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      linarith
    · change c < (D.cap i).cutHeight at hm
      rw [abs_of_pos (sub_pos.mpr hm)] at hr
      refine Or.inr ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      linarith
  have hseamHeight (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 = 0) :
      f ((D.cap i).sourceChart p) = ell i := by
    have hm := surgeryCapModel_cylinder
      (D.cap i).profile.horizontal (D.cap i).profile.vertical
      (D.cap i).profile.horizontal_smooth (D.cap i).profile.vertical_smooth
      (fun z => ((D.cap i).profile.horizontal_pos z).ne')
      (fun x => ((D.cap i).profile.vertical_pos x).ne')
      (D.cap i).profile.horizontal_near (D.cap i).profile.vertical_far p
      (by rw [hp]; norm_num)
    have hm0 : ((D.cap i).profile.model p).2 = 0 :=
      (congrArg Prod.snd hm).trans hp
    have ht : (((D.cap i).profile.model p).1,
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2)) ∈
        (D.cap i).tube.source := (D.cap i).tube_source
      ⟨mem_closedBall_zero_iff.mpr ((D.cap i).profile.model_fst_norm_le p), mem_univ _⟩
    dsimp only [f]
    rw [(D.cap i).central_eq p (by rw [hp]; exact (D.cap i).overlap_pos),
      SurgeryCapProfile.capMap_apply, (D.cap i).tube_height _ ht, hm0]
    dsimp only [ell]
    ring
  have hsouth (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 < 0) :
      (D.cap i).sourceChart p ∉ D.sourceCore := by
    intro hk
    have hc : (D.cap i).sourceChart p ∈ (D.cap i).sourceCap := ⟨p, hp.le, rfl⟩
    have hs : (D.cap i).sourceChart p ∈ (D.cap i).sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hk, hc⟩
    obtain ⟨q, hq, heq⟩ := hs
    have hqp := (D.cap i).sourceChart.injOn
      ((D.cap i).south_mem_source q hq.le) ((D.cap i).south_mem_source p hp.le) heq
    rw [hqp] at hq
    change (heightCoordinates (p : E3)).2 = 0 at hq
    linarith
  have hgap (i : Fin D.capCount) : 2 * delta < |ell i - c| := by
    by_contra hn
    have hg : |ell i - c| ≤ 2 * delta := le_of_not_gt hn
    have : Nonempty UnitCircle := (NormedSpace.sphere_nonempty
      (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
    let theta : UnitCircle := Classical.choice this
    let p : ℝ → UnitTwoSphere := fun a => northSpherePoint ((1 + a) • (theta : E2))
    have hp : Continuous p := northSpherePoint_contMDiff.continuous.comp
      ((continuous_const.add continuous_id).smul continuous_const)
    have hp0 : (heightCoordinates (p 0 : E3)).2 = 0 := by
      simpa only [p, add_zero, one_smul] using congrArg Prod.snd (northSpherePoint_equator theta)
    have hps : p 0 ∈ (D.cap i).sourceChart.source := (D.cap i).south_mem_source _ hp0.le
    have hfc : ContinuousAt (fun a : ℝ => |f ((D.cap i).sourceChart (p a)) - c|) 0 :=
      ((hf.continuousAt.comp
        (((D.cap i).sourceChart.continuousOn.continuousAt
          ((D.cap i).sourceChart.open_source.mem_nhds hps)).comp hp.continuousAt)).sub
        continuousAt_const).abs
    have hlt : |f ((D.cap i).sourceChart (p 0)) - c| < 3 * delta := by
      rw [hseamHeight i (p 0) hp0]
      linarith
    have hev : ∀ᶠ a : ℝ in 𝓝 0, |f ((D.cap i).sourceChart (p a)) - c| < 3 * delta :=
      hfc.eventually (isOpen_Iio.mem_nhds hlt)
    obtain ⟨eps, heps, hsub⟩ := Metric.mem_nhds_iff.mp hev
    have he : eps / 2 ∈ ball (0 : ℝ) eps := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hneg : (heightCoordinates (p (eps / 2) : E3)).2 < 0 := by
      apply lt_of_not_ge
      intro hnative
      have hx := (northSpherePoint_height_nonneg_iff ((1 + eps / 2) • (theta : E2))).mp hnative
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), norm_eq_of_mem_sphere theta,
        mul_one] at hx
      linarith
    exact hsouth i (p (eps / 2)) hneg (hcore _ (hsub he).le)
  have hmseams (i : Fin D.capCount) (hi : (D.cap i).sign = 1) : ell i < c - 2 * delta := by
    rcases hsides i with ⟨_, hs⟩ | ⟨heq, _⟩
    · have hg := hgap i
      rw [abs_of_neg (sub_neg.mpr hs)] at hg
      linarith
    · rw [hi] at heq
      norm_num at heq
  have hpseams (i : Fin D.capCount) (hi : (D.cap i).sign = -1) : c + 2 * delta < ell i := by
    rcases hsides i with ⟨heq, _⟩ | ⟨_, hs⟩
    · rw [hi] at heq
      norm_num at heq
    · have hg := hgap i
      rw [abs_of_pos (sub_pos.mpr hs)] at hg
      linarith
  have rmExists := exists_saddle_core_truncation_retraction psi hpsi u D
    (-1) (c - delta) (by norm_num) (by change 0 < -1 * (c - delta - c); linarith)
    (fun i hi => by
      have hh := hmseams i (by simpa only [neg_neg] using hi)
      change 0 < -1 * (ell i - (c - delta))
      linarith)
  simp only [neg_one_mul, neg_sub, sub_nonneg] at rmExists
  change ∃ rm : UnitTwoSphere → UnitTwoSphere,
    ContMDiff (𝓡 2) (𝓡 2) ∞ rm ∧ La ⊆ Km ∧ MapsTo rm Km La ∧ EqOn rm id La at rmExists
  obtain ⟨rm, hrm, hLa, hmmap, hmfix⟩ := rmExists
  have rpExists := exists_saddle_core_truncation_retraction psi hpsi u D
    1 (c + delta) (by norm_num) (by change 0 < 1 * (c + delta - c); linarith)
    (fun i hi => by
      have hh := hpseams i hi
      change 0 < 1 * (ell i - (c + delta))
      linarith)
  simp only [one_mul, sub_nonneg] at rpExists
  change ∃ rp : UnitTwoSphere → UnitTwoSphere,
    ContMDiff (𝓡 2) (𝓡 2) ∞ rp ∧ Lb ⊆ Kp ∧ MapsTo rp Kp Lb ∧ EqOn rp id Lb at rpExists
  obtain ⟨rp, hrp, _hLb, hpmap, hpfix⟩ := rpExists
  have hfixm (q : UnitTwoSphere) (hq : q ∈ La) : rm q = q := hmfix hq
  have hfixp (q : UnitTwoSphere) (hq : q ∈ Lb) : rp q = q := hpfix hq
  obtain ⟨F, M, L, hM, hL, hF, hcF, _support, _, _, _, hPhi, _, _, _, hS,
    _, _, hVo, hC0, hclosure, _, hwall, hwallflow, hlevels⟩ :=
    exists_saddle_selected_wall_transport psi hpsi u D R delta hR hdelta hdeltaR hmorse hcore N hN
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph F hM hL hF hcF t
  let Elevel : ℝ → Set E3 := fun t =>
    (range j ∩ {y | H y = c + t}) \ (j '' V)
  let q4 : Fin 4 → ℝ → UnitTwoSphere := fun i t => D.morse.symm (N
    (![1, -1, -1, 1] i * Real.sqrt ((rho ^ 2 * (1 + (0 : ℝ)) ^ 2 + t) / 2),
      ![1, 1, -1, -1] i * Real.sqrt ((rho ^ 2 * (1 + (0 : ℝ)) ^ 2 - t) / 2)))
  change ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) at hPhi
  change ∀ t : ℝ, Phi t '' range j = range j ∧ (Phi t).symm '' range j = range j at hS
  change IsOpen V at hVo
  change IsCompact C0 at hC0
  change closure V = C0 at hclosure
  have hVC : V ⊆ C0 := hclosure ▸ subset_closure
  change ∀ t : ℝ, |t| ≤ 2 * delta →
    {p : UnitTwoSphere | p ∈ C0 \ V ∧ f p = c + t} = range (fun i => q4 i t) at hwall
  have hwallmove (i : Fin 4) (s t : ℝ) (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta) :
      Phi (t - s) (j (q4 i s)) = j (q4 i t) := hwallflow i 0 (by norm_num) s t hs ht
  change ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
    Phi (t - s) '' Elevel s = Elevel t ∧
    (Phi (t - s)).symm '' Elevel t = Elevel s at hlevels
  have hflowS (t : ℝ) (q : UnitTwoSphere) : Phi t (j q) ∈ range j := by
    rw [← (hS t).1]
    exact ⟨j q, mem_range_self q, rfl⟩
  obtain ⟨e, he, hes, het, hei⟩ := exists_collar_chart psi hpsi
  have hej (q : UnitTwoSphere) : e.symm (j q) = (q, 0) := by
    calc
      e.symm (j q) = e.symm (e (q, 0)) := congrArg e.symm (congrFun he (q, 0)).symm
      _ = (q, 0) := e.left_inv (by rw [hes]; exact ⟨mem_univ _, by norm_num⟩)
  have htarget (t : ℝ) (q : UnitTwoSphere) : Phi t (j q) ∈ e.target := by
    rw [het]
    obtain ⟨p, hp⟩ := hflowS t q
    exact ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, hp⟩
  let P : ℝ × UnitTwoSphere → UnitTwoSphere := fun p => (e.symm (Phi p.1 (j p.2))).1
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P := by
    apply contMDiffOn_univ.mp
    have hi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞ (fun y => (e.symm y).1) e.target :=
      contMDiff_fst.comp_contMDiffOn hei
    have ha : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
        (fun p : ℝ × UnitTwoSphere => Phi p.1 (j p.2)) :=
      hPhi.contMDiff.comp (contMDiff_fst.prodMk_space (hj.comp contMDiff_snd))
    exact hi.comp ha.contMDiffOn (fun p _ => htarget p.1 p.2)
  have hPimage (t : ℝ) (q : UnitTwoSphere) : j (P (t, q)) = Phi t (j q) := by
    obtain ⟨p, hp⟩ := hflowS t q
    change j ((e.symm (Phi t (j q))).1) = Phi t (j q)
    rw [← hp, hej]
  have hPzero (q : UnitTwoSphere) : P (0, q) = q := by
    change (e.symm (boundedFlow F hM hL (j q) 0)).1 = q
    rw [boundedFlow_zero, hej]
  have hPinj (t : ℝ) : Injective (fun q => P (t, q)) := by
    intro p q hpq
    apply hji
    apply (Phi t).injective
    change Phi t (j p) = Phi t (j q)
    exact (hPimage t p).symm.trans ((congrArg j hpq).trans (hPimage t q))
  have hPneg (t : ℝ) (q : UnitTwoSphere) : P (-t, P (t, q)) = q := by
    apply hji
    rw [hPimage, hPimage]
    exact boundedFlow_neg F hM hL (j q) t
  let Y : ℝ → Set UnitTwoSphere := fun t => {q | f q = c + t} \ V
  have hmemE (t : ℝ) (q : UnitTwoSphere) : j q ∈ Elevel t ↔ q ∈ Y t := by
    constructor
    · intro hq
      exact ⟨hq.1.2, fun hv => hq.2 ⟨q, hv, rfl⟩⟩
    · intro hq
      refine ⟨⟨mem_range_self q, hq.1⟩, ?_⟩
      rintro ⟨p, hp, hpq⟩
      exact hq.2 ((hji hpq) ▸ hp)
  have hmove (s t : ℝ) (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta)
      (q : UnitTwoSphere) (hq : q ∈ Y s) : P (t - s, q) ∈ Y t := by
    apply (hmemE t _).mp
    rw [hPimage, ← (hlevels s t hs ht).1]
    exact ⟨j q, (hmemE s q).mpr hq, rfl⟩
  let It : Set ℝ := Icc (-delta) delta
  let T : ℝ × UnitTwoSphere → UnitTwoSphere := fun p => P (p.1 + delta, p.2)
  have hTc : Continuous T := hP.continuous.comp
    ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have htime (t : ℝ) (ht : t ∈ It) : |t| ≤ 2 * delta := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  have hmTime : |-delta| ≤ 2 * delta := by rw [abs_neg, abs_of_pos hdelta]; linarith
  have hTmem (t : ℝ) (ht : t ∈ It) (q : UnitTwoSphere) (hq : q ∈ Y (-delta)) :
      T (t, q) ∈ Y t := by
    simpa only [T, sub_neg_eq_add] using hmove (-delta) t hmTime (htime t ht) q hq
  have hTheight (t : ℝ) (ht : t ∈ It) (q : UnitTwoSphere) (hq : q ∈ Y (-delta)) :
      f (T (t, q)) = c + t := (hTmem t ht q hq).1
  have hTzero (q : UnitTwoSphere) : T (-delta, q) = q := by
    simp only [T, neg_add_cancel, hPzero]
  have hTinj (t : ℝ) : Injective (fun q => T (t, q)) := hPinj (t + delta)
  have hTinverse (t : ℝ) (ht : t ∈ It) (q : UnitTwoSphere) (hq : q ∈ Y t) :
      ∃ p ∈ Y (-delta), T (t, p) = q := by
    refine ⟨P (-(t + delta), q), ?_, ?_⟩
    · simpa only [show -delta - t = -(t + delta) by ring] using
        hmove t (-delta) (htime t ht) hmTime q hq
    · simpa only [T, neg_neg] using hPneg (-(t + delta)) q
  have hTavoid (t : ℝ) (ht : t ∈ It) (p : UnitTwoSphere)
      (hp : p ∈ Y (-delta)) (hpc : p ∉ C0) : T (t, p) ∉ C0 := by
    intro htc
    have hw : T (t, p) ∈ range (fun i => q4 i t) := by
      rw [← hwall t (htime t ht)]
      exact ⟨⟨htc, (hTmem t ht p hp).2⟩, hTheight t ht p hp⟩
    obtain ⟨i, hi⟩ := hw
    have hbase : q4 i (-delta) ∈ C0 := by
      have hw0 : q4 i (-delta) ∈ {q : UnitTwoSphere | q ∈ C0 \ V ∧ f q = c + -delta} := by
        rw [hwall (-delta) hmTime]
        exact mem_range_self i
      exact hw0.1.1
    have hEq : Phi (t + delta) (j (q4 i (-delta))) = Phi (t + delta) (j p) := by
      calc
        _ = j (q4 i t) := by
          simpa only [sub_neg_eq_add] using hwallmove i (-delta) t hmTime (htime t ht)
        _ = j (T (t, p)) := congrArg j hi
        _ = _ := hPimage (t + delta) p
    exact hpc ((hji ((Phi (t + delta)).injective hEq)) ▸ hbase)
  intro B hBLa hBc hBrc hBC
  let Band : Set UnitTwoSphere := {q | f q ∈ Icc (c - delta) (c + delta)}
  let E : Set UnitTwoSphere := (La \ B) \ V
  let ZB : Set UnitTwoSphere := T '' (It ×ˢ B)
  let ZR : Set UnitTwoSphere := (Band ∩ C0) ∪ T '' (It ×ˢ E)
  let Bb : Set UnitTwoSphere := (fun p => T (delta, p)) '' B
  have hBandc : IsCompact Band := (isClosed_Icc.preimage hf).isCompact
  have hBandK : Band ⊆ D.sourceCore := by
    intro q hq
    apply hcore
    apply abs_le.mpr
    constructor <;> linarith [hq.1, hq.2]
  have hLaband : La ⊆ Band := fun q hq => by
    change f q = c - delta at hq
    exact ⟨by linarith, by linarith⟩
  have hLbband : Lb ⊆ Band := fun q hq => by
    change f q = c + delta at hq
    exact ⟨by linarith, by linarith⟩
  have hBY : B ⊆ Y (-delta) := by
    intro p hp
    refine ⟨?_, fun hv => Set.disjoint_left.mp hBC hp (hVC hv)⟩
    have hh : f p = c - delta := hBLa hp
    change f p = c + -delta
    simpa only [sub_eq_add_neg] using hh
  have hEY : E ⊆ Y (-delta) := by
    intro p hp
    have hh : f p = c - delta := hp.1.1
    exact ⟨by change f p = c + -delta; simpa only [sub_eq_add_neg] using hh, hp.2⟩
  have hEc : IsCompact E := hBrc.inter_right hVo.isClosed_compl
  have hZBc : IsCompact ZB := (isCompact_Icc.prod hBc).image hTc
  have hZRc : IsCompact ZR := (hBandc.inter_right hC0.isClosed).union
    ((isCompact_Icc.prod hEc).image hTc)
  have hBbc : IsCompact Bb := hBc.image (hTc.comp (continuous_const.prodMk continuous_id))
  have hTband (t : ℝ) (ht : t ∈ It) (p : UnitTwoSphere) (hp : p ∈ Y (-delta)) :
      T (t, p) ∈ Band := by
    change c - delta ≤ f (T (t, p)) ∧ f (T (t, p)) ≤ c + delta
    rw [hTheight t ht p hp]
    constructor <;> linarith [ht.1, ht.2]
  have hZBband : ZB ⊆ Band := by
    rintro q ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩
    exact hTband t ht p (hBY hp)
  have hZRband : ZR ⊆ Band := by
    rintro q (hq | ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩)
    · exact hq.1
    · exact hTband t ht p (hEY hp)
  have hZD : Disjoint ZB ZR := by
    apply Set.disjoint_left.mpr
    rintro q ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩ (hq | ⟨⟨s, v⟩, ⟨hs, hv⟩, heq⟩)
    · exact hTavoid t ht p (hBY hp) (fun hh => Set.disjoint_left.mp hBC hp hh) hq.2
    · have hst : s = t := by
        have hh := congrArg f heq
        rw [hTheight s hs v (hEY hv), hTheight t ht p (hBY hp)] at hh
        linarith
      subst s
      have hvp := hTinj t heq
      exact hv.1.2 (hvp.symm ▸ hp)
  have hcover : ZB ∪ ZR = Band := by
    apply Subset.antisymm
    · exact union_subset hZBband hZRband
    · intro q hq
      by_cases hqc : q ∈ C0
      · exact Or.inr (Or.inl ⟨hq, hqc⟩)
      have ht : f q - c ∈ It := ⟨by linarith [hq.1], by linarith [hq.2]⟩
      have hqy : q ∈ Y (f q - c) :=
        ⟨by change f q = c + (f q - c); ring, fun hv => hqc (hVC hv)⟩
      obtain ⟨p, hp, hpq⟩ := hTinverse (f q - c) ht q hqy
      by_cases hpB : p ∈ B
      · exact Or.inl ⟨(f q - c, p), ⟨ht, hpB⟩, hpq⟩
      · have hpa : p ∈ La := by
          change f p = c - delta
          simpa only [sub_eq_add_neg] using (show f p = c + -delta from hp.1)
        exact Or.inr (Or.inr ⟨(f q - c, p), ⟨ht, ⟨⟨hpa, hpB⟩, hp.2⟩⟩, hpq⟩)
  have hZBa : ZB ∩ La = B := by
    ext q
    constructor
    · rintro ⟨⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩, hq⟩
      have hh := hTheight t ht p (hBY hp)
      change f (T (t, p)) = c - delta at hq
      have htm : t = -delta := by linarith
      subst t
      simpa only [hTzero] using hp
    · intro hq
      exact ⟨⟨(-delta, q), ⟨⟨le_rfl, by linarith⟩, hq⟩, hTzero q⟩, hBLa hq⟩
  have hZBb : ZB ∩ Lb = Bb := by
    ext q
    constructor
    · rintro ⟨⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩, hq⟩
      have hh := hTheight t ht p (hBY hp)
      change f (T (t, p)) = c + delta at hq
      have htp : t = delta := by linarith
      subst t
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨(delta, p), ⟨⟨by linarith, le_rfl⟩, hp⟩, rfl⟩,
        hTheight delta ⟨by linarith, le_rfl⟩ p (hBY hp)⟩
  have hcomplement (A : Set UnitTwoSphere) (hA : A ⊆ Band) :
      ZR ∩ A = A \ (ZB ∩ A) := by
    ext q
    constructor
    · rintro ⟨hr, ha⟩
      exact ⟨ha, fun hb => Set.disjoint_left.mp hZD hb.1 hr⟩
    · rintro ⟨ha, hn⟩
      have hc : q ∈ ZB ∪ ZR := hcover.symm ▸ hA ha
      rcases hc with hb | hr
      · exact False.elim (hn ⟨hb, ha⟩)
      · exact ⟨hr, ha⟩
  have hZRa : ZR ∩ La = La \ B := by rw [hcomplement La hLaband, hZBa]
  have hZRb : ZR ∩ Lb = Lb \ Bb := by rw [hcomplement Lb hLbband, hZBb]
  have hLbc : IsClosed Lb := isClosed_eq hf continuous_const
  have hBbrc : IsCompact (Lb \ Bb) := hZRb ▸ hZRc.inter_right hLbc
  have hKmc : IsCompact Km := D.sourceCore_compact.inter_right (isClosed_le hf continuous_const)
  have hKpc : IsCompact Kp := D.sourceCore_compact.inter_right (isClosed_le continuous_const hf)
  let MB : Set UnitTwoSphere := Km ∩ rm ⁻¹' B
  let MR : Set UnitTwoSphere := Km ∩ rm ⁻¹' (La \ B)
  let PB : Set UnitTwoSphere := Kp ∩ rp ⁻¹' Bb
  let PR : Set UnitTwoSphere := Kp ∩ rp ⁻¹' (Lb \ Bb)
  let TB : Set UnitTwoSphere := (MB ∪ ZB) ∪ PB
  let TR : Set UnitTwoSphere := (MR ∪ ZR) ∪ PR
  have hTBc : IsCompact TB :=
    ((hKmc.inter_right (hBc.isClosed.preimage hrm.continuous)).union hZBc).union
      (hKpc.inter_right (hBbc.isClosed.preimage hrp.continuous))
  have hTRc : IsCompact TR :=
    ((hKmc.inter_right (hBrc.isClosed.preimage hrm.continuous)).union hZRc).union
      (hKpc.inter_right (hBbrc.isClosed.preimage hrp.continuous))
  have hlow (q : UnitTwoSphere) (hq : q ∈ Km) (hb : q ∈ Band) : q ∈ La := by
    change f q = c - delta
    exact le_antisymm hq.2 hb.1
  have hupp (q : UnitTwoSphere) (hq : q ∈ Kp) (hb : q ∈ Band) : q ∈ Lb := by
    change f q = c + delta
    exact le_antisymm hb.2 hq.2
  have hTD : Disjoint TB TR := by
    apply Set.disjoint_left.mpr
    intro q hq hr
    rcases hq with (hm | hz) | hp <;> rcases hr with (hm' | hz') | hp'
    · exact hm'.2.2 hm.2
    · have ha := hlow q hm.1 (hZRband hz')
      have hn : q ∈ La \ B := hZRa ▸ ⟨hz', ha⟩
      have hb : rm q ∈ B := hm.2
      rw [hfixm q ha] at hb
      exact hn.2 hb
    · have hmle : f q ≤ c - delta := hm.1.2
      have hple : c + delta ≤ f q := hp'.1.2
      linarith
    · have ha := hlow q hm'.1 (hZBband hz)
      have hb : q ∈ B := hZBa ▸ ⟨hz, ha⟩
      have hn : rm q ∉ B := hm'.2.2
      rw [hfixm q ha] at hn
      exact hn hb
    · exact Set.disjoint_left.mp hZD hz hz'
    · have hb := hupp q hp'.1 (hZBband hz)
      have hqB : q ∈ Bb := hZBb ▸ ⟨hz, hb⟩
      have hn : rp q ∉ Bb := hp'.2.2
      rw [hfixp q hb] at hn
      exact hn hqB
    · have hmle : f q ≤ c - delta := hm'.1.2
      have hple : c + delta ≤ f q := hp.1.2
      linarith
    · have hb := hupp q hp.1 (hZRband hz')
      have hn : q ∈ Lb \ Bb := hZRb ▸ ⟨hz', hb⟩
      have hqB : rp q ∈ Bb := hp.2
      rw [hfixp q hb] at hqB
      exact hn.2 hqB
    · exact hp'.2.2 hp.2
  have hfull : TB ∪ TR = D.sourceCore := by
    apply Subset.antisymm
    · intro q hq
      rcases hq with ((hm | hz) | hp) | ((hm | hz) | hp)
      · exact hm.1.1
      · exact hBandK (hZBband hz)
      · exact hp.1.1
      · exact hm.1.1
      · exact hBandK (hZRband hz)
      · exact hp.1.1
    · intro q hq
      by_cases hm : f q ≤ c - delta
      · have hqm : q ∈ Km := ⟨hq, hm⟩
        by_cases hb : rm q ∈ B
        · exact Or.inl (Or.inl (Or.inl ⟨hqm, hb⟩))
        · exact Or.inr (Or.inl (Or.inl ⟨hqm, ⟨hmmap hqm, hb⟩⟩))
      by_cases hp : c + delta ≤ f q
      · have hqp : q ∈ Kp := ⟨hq, hp⟩
        by_cases hb : rp q ∈ Bb
        · exact Or.inl (Or.inr ⟨hqp, hb⟩)
        · exact Or.inr (Or.inr ⟨hqp, ⟨hpmap hqp, hb⟩⟩)
      have hb : q ∈ Band := ⟨(lt_of_not_ge hm).le, (lt_of_not_ge hp).le⟩
      have hz : q ∈ ZB ∪ ZR := hcover.symm ▸ hb
      rcases hz with hz | hz
      · exact Or.inl (Or.inl (Or.inr hz))
      · exact Or.inr (Or.inl (Or.inr hz))
  have hpointBand : D.point ∈ Band := by
    change c - delta ≤ c ∧ c ≤ c + delta
    constructor <;> linarith
  have hpointC : D.point ∈ C0 := by
    have hs := (D.protected_closure (subset_closure D.point_mem_protected)).1
    refine ⟨0, ?_, ?_⟩
    · change (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ rho ^ 2
      nlinarith [sq_nonneg rho]
    · calc
        D.morse.symm 0 = D.morse.symm (D.morse D.point) :=
          congrArg D.morse.symm D.morse_point.symm
        _ = D.point := D.morse.left_inv hs
  have hpointTR : D.point ∈ TR := Or.inl (Or.inr (Or.inl ⟨hpointBand, hpointC⟩))
  have hclosedDisjoint : D.sourceCore ∩ (TB ∩ TR) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact Set.disjoint_left.mp hTD hq.2.1 hq.2.2
  have hchoice := (isPreconnected_iff_subset_of_disjoint_closed.mp D.sourceCore_connected.2)
    TB TR hTBc.isClosed hTRc.isClosed hfull.ge hclosedDisjoint
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqa := hBLa hq
  have hqK : q ∈ D.sourceCore := (hLa hqa).1
  have hqTB : q ∈ TB := Or.inl (Or.inl ⟨hLa hqa, by
    change rm q ∈ B
    rw [hfixm q hqa]
    exact hq⟩)
  rcases hchoice with h | h
  · exact Set.disjoint_left.mp hTD (h (hBandK hpointBand)) hpointTR
  · exact Set.disjoint_left.mp hTD hqTB (h hqK)

end PoincareConjecture.M25.Topology3D
