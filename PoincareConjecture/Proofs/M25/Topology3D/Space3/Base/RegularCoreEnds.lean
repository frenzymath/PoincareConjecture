import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreSeamFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreExtrema
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.regular_core_cap_eq_of_sign_eq
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (z0 : ℝ)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (F : E3 → E3) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (L M : ℝ≥0) (hL : LipschitzWith L F) (hM : ∀ y : E3, ‖F y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U) (hcoreU : S.retainedCore i ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), F y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow F hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0)))
    (a b : Fin S.capCount) (ha : S.owner a = i) (hb : S.owner b = i)
    (hsign : (S.cap a).sign = (S.cap b).sign) :
    a = b := by
  classical
  let s : Fin S.capCount → ℝ := fun c =>
    (S.cap c).cutHeight + (S.cap c).sign * (S.cap c).removal
  let flow : E3 → ℝ → E3 := boundedFlow F hL hM
  have hcflow : Continuous (fun p : E3 × ℝ => flow p.1 p.2) :=
    (boundedFlow_contDiff F hL hM hF hFc).continuous
  have hcurve (x : E3) : Continuous (flow x) :=
    hcflow.comp (continuous_const.prodMk continuous_id)
  obtain ⟨_hK, _hconn, _hdef, _hcover, hinter⟩ := S.retainedCore_geometry i
  have hseam (c : Fin S.capCount) (hc : S.owner c = i)
      (x : E3) (hx : x ∈ (S.cap c).seam) :
      x ∈ S.retainedCore i ∧ ⟪(u : E3), x⟫_ℝ = s c := by
    have hxc : x ∈ S.retainedCore i ∩ (S.cap c).cap := by
      rw [hinter c hc]
      exact hx
    have hn : (S.cap c).sign ≠ 0 := by
      intro hz
      have h := (S.cap c).sign_abs
      rw [hz, abs_zero] at h
      norm_num at h
    have hh := ((S.cap c).cap_seam_signed_height x hxc.2).2.1.mpr hx
    exact ⟨hxc.1, sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn)⟩
  have hlocal (c : Fin S.capCount) (hc : S.owner c = i)
      (x : E3) (hx : x ∈ (S.cap c).seam) :
      ∃ O : Set E3, IsOpen O ∧ x ∈ O ∧
        ∀ y ∈ O, y ∈ S.retainedCore i →
          0 ≤ (S.cap c).sign * (⟪(u : E3), y⟫_ℝ - s c) := by
    let C := S.cap c
    obtain ⟨q0, hq0, hq0x⟩ := hx
    have hq0x' : psi i (q0, 0) = x := by simpa only [hc] using hq0x
    obtain ⟨W, hW, hqW, _hWt, _hWi, hWform⟩ :=
      S.exists_seam_source_half_neighborhood c q0 hq0
    obtain ⟨E, hEf, hEs, _hEt, _hEi⟩ := exists_collar_chart (psi i) (S.embedding i)
    have hsource (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ E.source := by
      rw [hEs]
      exact ⟨mem_univ _, by norm_num⟩
    have hval (q : UnitTwoSphere) : E (q, 0) = psi i (q, 0) := congrFun hEf (q, 0)
    have htarget (q : UnitTwoSphere) : psi i (q, 0) ∈ E.target := by
      rw [← hval]
      exact E.map_source (hsource q)
    have hinverse (q : UnitTwoSphere) : E.symm (psi i (q, 0)) = (q, 0) := by
      rw [← hval]
      exact E.left_inv (hsource q)
    let O : Set E3 := E.target ∩ E.symm ⁻¹' (W ×ˢ (univ : Set ℝ))
    have hO : IsOpen O := E.symm.continuousOn.isOpen_inter_preimage E.open_target
      (hW.prod isOpen_univ)
    refine ⟨O, hO, ?_, ?_⟩
    · rw [← hq0x']
      refine ⟨htarget q0, ?_⟩
      change E.symm (psi i (q0, 0)) ∈ W ×ˢ (univ : Set ℝ)
      rw [hinverse]
      exact ⟨hqW, mem_univ _⟩
    · rintro y hy ⟨q, hqCore, rfl⟩
      have hqW' : q ∈ W := by
        have h := hy.2
        change E.symm (psi i (q, 0)) ∈ W ×ˢ (univ : Set ℝ) at h
        rw [hinverse] at h
        exact h.1
      obtain ⟨_hp, _hz1, _hz2, _hinv, _hxi, _heq, hheight, hcore, _hqs, _hother⟩ :=
        hWform q hqW'
      let z := (heightCoordinates ((C.sourceChart.symm q : UnitTwoSphere) : E3)).2
      have hqOwner : q ∈ S.sourceCore (S.owner c) := by simpa only [hc] using hqCore
      have hz : 0 ≤ z := hcore.mp hqOwner
      have hheight' : ⟪(u : E3), psi i (q, 0)⟫_ℝ = s c + C.sign * (C.scale * z) := by
        calc
          _ = C.cutHeight + C.sign * (C.removal + C.scale * z) := by
            simpa only [hc] using hheight
          _ = _ := by dsimp only [s, C]; ring
      have hsignsq : C.sign * C.sign = 1 := by nlinarith [C.sign_abs, sq_abs C.sign]
      have hprod : C.sign * (⟪(u : E3), psi i (q, 0)⟫_ℝ - s c) = C.scale * z := by
        calc
          _ = (C.sign * C.sign) * (C.scale * z) := by rw [hheight']; ring
          _ = _ := by rw [hsignsq, one_mul]
      change 0 ≤ C.sign * (⟪(u : E3), psi i (q, 0)⟫_ℝ - s c)
      rw [hprod]
      exact mul_nonneg C.scale_pos.le hz
  have himage (c : Fin S.capCount) (hc : S.owner c = i) :
      (fun y => flow y (z0 - s c)) '' (S.cap c).seam =
        collarHeightLevel (psi i) (u : E3) z0 := by
    obtain ⟨_hcompact, _hne, _hsub, _hopen, heq⟩ :=
      S.regular_core_seam_middle_image i z0 hlower hupper F hF hFc L M hL hM
        U hU hcoreU hunit hsphere c hc
    exact heq
  obtain ⟨q, hq⟩ := (S.cap a).sourceSeam_isConnected.nonempty
  let xa := psi (S.owner a) (q, 0)
  have hxa : xa ∈ (S.cap a).seam := ⟨q, hq, rfl⟩
  have hyb : flow xa (z0 - s a) ∈ (fun y => flow y (z0 - s b)) '' (S.cap b).seam := by
    rw [himage b hb, ← himage a ha]
    exact ⟨xa, hxa, rfl⟩
  obtain ⟨xb, hxb, heq⟩ := hyb
  change flow xb (z0 - s b) = flow xa (z0 - s a) at heq
  have hrel : flow xa (s b - s a) = xb := by
    calc
      _ = flow (flow xa (z0 - s a)) (-(z0 - s b)) := by
        change boundedFlow F hL hM xa (s b - s a) =
          boundedFlow F hL hM (boundedFlow F hL hM xa (z0 - s a)) (-(z0 - s b))
        rw [← boundedFlow_add]
        congr 1
        ring
      _ = flow (flow xb (z0 - s b)) (-(z0 - s b)) := by rw [heq]
      _ = xb := boundedFlow_neg F hL hM xb (z0 - s b)
  have hrel' : flow xb (s a - s b) = xa := by
    calc
      _ = flow (flow xa (s b - s a)) (-(s b - s a)) := by
        rw [hrel]
        congr 1
        ring
      _ = xa := boundedFlow_neg F hL hM xa (s b - s a)
  have hno (c d : Fin S.capCount) (hc : S.owner c = i) (hd : S.owner d = i)
      (hcdsign : (S.cap c).sign = (S.cap d).sign)
      (x y : E3) (hx : x ∈ (S.cap c).seam) (hy : y ∈ (S.cap d).seam)
      (hxy : flow x (s d - s c) = y) (hyx : flow y (s c - s d) = x)
      (hcd : s c < s d) : False := by
    have hs : (S.cap c).sign = 1 ∨ (S.cap c).sign = -1 := by
      apply abs_eq_abs.mp
      simpa only [abs_one] using (S.cap c).sign_abs
    rcases hs with hs | hs
    · have hds : (S.cap d).sign = 1 := hcdsign.symm.trans hs
      have hbound : s d < z0 := hlower d hd hds
      obtain ⟨O, hO, hyO, hineq⟩ := hlocal d hd y hy
      have hpre : IsOpen ((flow x) ⁻¹' O) := hO.preimage (hcurve x)
      obtain ⟨eta, heta, hball⟩ := Metric.isOpen_iff.mp hpre (s d - s c)
        (by change flow x (s d - s c) ∈ O; rw [hxy]; exact hyO)
      obtain ⟨eps, heps, hepslt⟩ := exists_between (lt_min heta (sub_pos.mpr hcd))
      have hepseta : eps < eta := hepslt.trans_le (min_le_left _ _)
      have hepsdelta : eps < s d - s c := hepslt.trans_le (min_le_right _ _)
      let t := s d - s c - eps
      have ht : t ∈ uIcc 0 (z0 - ⟪(u : E3), x⟫_ℝ) := by
        rw [(hseam c hc x hx).2, uIcc_of_le (by linarith : 0 ≤ z0 - s c)]
        dsimp only [t]
        constructor <;> linarith only [hepsdelta, heps, hbound]
      have hpointO : flow x t ∈ O := by
        apply hball
        rw [mem_ball, Real.dist_eq]
        have ht' : t - (s d - s c) = -eps := by dsimp only [t]; ring
        rw [ht', abs_neg, abs_of_pos heps]
        exact hepseta
      obtain ⟨hpointK, hh⟩ := S.regular_core_flow_segment i z0 hlower hupper
        F L M hL hM U hU hcoreU hunit hsphere x (hseam c hc x hx).1 t ht
      have hi := hineq (flow x t) hpointO hpointK
      rw [hds, one_mul] at hi
      rw [(hseam c hc x hx).2] at hh
      dsimp only [t] at hh
      change ⟪(u : E3), flow x (s d - s c - eps)⟫_ℝ = s c + (s d - s c - eps) at hh
      dsimp only [t] at hi
      linarith only [hi, hh, heps]
    · have hbound : z0 < s c := hupper c hc hs
      obtain ⟨O, hO, hxO, hineq⟩ := hlocal c hc x hx
      have hpre : IsOpen ((flow y) ⁻¹' O) := hO.preimage (hcurve y)
      obtain ⟨eta, heta, hball⟩ := Metric.isOpen_iff.mp hpre (s c - s d)
        (by change flow y (s c - s d) ∈ O; rw [hyx]; exact hxO)
      obtain ⟨eps, heps, hepslt⟩ := exists_between
        (lt_min heta (show 0 < -(s c - s d) from by linarith only [hcd]))
      have hepseta : eps < eta := hepslt.trans_le (min_le_left _ _)
      have hepsdelta : eps < -(s c - s d) := hepslt.trans_le (min_le_right _ _)
      let t := s c - s d + eps
      have ht : t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ) := by
        rw [(hseam d hd y hy).2, uIcc_of_ge (by linarith : z0 - s d ≤ 0)]
        dsimp only [t]
        constructor <;> linarith only [hepsdelta, heps, hbound]
      have hpointO : flow y t ∈ O := by
        apply hball
        rw [mem_ball, Real.dist_eq]
        have ht' : t - (s c - s d) = eps := by dsimp only [t]; ring
        rw [ht', abs_of_pos heps]
        exact hepseta
      obtain ⟨hpointK, hh⟩ := S.regular_core_flow_segment i z0 hlower hupper
        F L M hL hM U hU hcoreU hunit hsphere y (hseam d hd y hy).1 t ht
      have hi := hineq (flow y t) hpointO hpointK
      rw [hs, neg_one_mul] at hi
      rw [(hseam d hd y hy).2] at hh
      dsimp only [t] at hh
      change ⟪(u : E3), flow y (s c - s d + eps)⟫_ℝ = s d + (s c - s d + eps) at hh
      dsimp only [t] at hi
      linarith only [hi, hh, heps]
  rcases lt_trichotomy (s a) (s b) with hlt | he | hgt
  · exact (hno a b ha hb hsign xa xb hxa hxb hrel hrel' hlt).elim
  · have hxab : xa = xb := by
      simpa only [he, sub_self, flow, boundedFlow_zero] using hrel
    by_contra hab
    have hxac : xa ∈ (S.cap a).cap := by
      have h := hxa
      rw [← hinter a ha] at h
      exact h.2
    have hxbc : xb ∈ (S.cap b).cap := by
      have h := hxb
      rw [← hinter b hb] at h
      exact h.2
    exact disjoint_left.mp (S.caps_disjoint hab) hxac (hxab.symm ▸ hxbc)
  · exact (hno b a hb ha hsign.symm xb xa hxb hxa hrel' hrel hgt).elim

theorem FamilyCutState.exists_regular_core_two_ends
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n)
    (hregular : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) :
    let seamHeight : Fin S.capCount → ℝ := fun a =>
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
    let nativeHeight : UnitTwoSphere → ℝ := fun q =>
      ⟪(u : E3), psi i (q, 0)⟫_ℝ
    ∃ (a b : Fin S.capCount) (p q : UnitTwoSphere) (z0 : ℝ),
      S.owner a = i ∧ S.owner b = i ∧ a ≠ b ∧
      (S.cap a).sign = 1 ∧ (S.cap b).sign = -1 ∧
      (∀ c : Fin S.capCount, S.owner c = i ↔ c = a ∨ c = b) ∧
      (∀ c : Fin S.capCount,
        S.owner c = i ∧ (S.cap c).sign = 1 ↔ c = a) ∧
      (∀ c : Fin S.capCount,
        S.owner c = i ∧ (S.cap c).sign = -1 ↔ c = b) ∧
      Fintype.card {c : Fin S.capCount // S.owner c = i} = 2 ∧
      p ∈ S.sourceCore i ∧ q ∈ S.sourceCore i ∧
      p ∈ (S.cap a).sourceSeam ∧ q ∈ (S.cap b).sourceSeam ∧
      IsMinOn nativeHeight (S.sourceCore i) p ∧
      IsMaxOn nativeHeight (S.sourceCore i) q ∧
      seamHeight a < z0 ∧ z0 < seamHeight b ∧
      (∀ x ∈ (S.cap a).sourceSeam, nativeHeight x = seamHeight a) ∧
      (∀ x ∈ (S.cap b).sourceSeam, nativeHeight x = seamHeight b) ∧
      ∀ x ∈ S.sourceCore i,
        seamHeight a ≤ nativeHeight x ∧ nativeHeight x ≤ seamHeight b := by
  classical
  dsimp only
  obtain ⟨z0, hlower, hupper⟩ := S.exists_common_seam_height hzero i
  obtain ⟨_rho, _hrho, _hrhoPsi, _hrhoNz, N, _hN, hKN, _hNU, _hNV,
    F, hF, hFc, _hFs, _hFrho, hunit, L, M, hL, hM, _hflow, hmap, _hfix⟩ :=
    S.exists_regular_core_flow_data i hregular
  have hunitU : ∀ y ∈ interior N, ⟪(u : E3), F y⟫_ℝ = 1 :=
    fun y hy => hunit y (interior_subset hy)
  have hsphere (y : E3) (hy : y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)))
      (t : ℝ) : boundedFlow F hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0)) := by
    rw [← hmap t]
    exact ⟨y, hy, rfl⟩
  have hsame (a b : Fin S.capCount) (ha : S.owner a = i) (hb : S.owner b = i)
      (hs : (S.cap a).sign = (S.cap b).sign) : a = b :=
    S.regular_core_cap_eq_of_sign_eq i z0 hlower hupper F hF hFc L M hL hM
      (interior N) isOpen_interior hKN hunitU hsphere a b ha hb hs
  obtain ⟨a, b, p, q, ha, hb, hab, hp, hq, hpa, hqb, hmin, hmax, hha, hhb, hlt⟩ :=
    S.exists_sourceCore_height_ends i hregular
  have hsig (c : Fin S.capCount) : (S.cap c).sign = 1 ∨ (S.cap c).sign = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using (S.cap c).sign_abs
  have hsigns : (S.cap a).sign = 1 ∧ (S.cap b).sign = -1 := by
    rcases hsig a with hsa | hsa <;> rcases hsig b with hsb | hsb
    · exact (hab (hsame a b ha hb (hsa.trans hsb.symm))).elim
    · exact ⟨hsa, hsb⟩
    · have hau := hupper a ha hsa
      have hbl := hlower b hb hsb
      exfalso
      linarith only [hau, hbl, hlt]
    · exact (hab (hsame a b ha hb (hsa.trans hsb.symm))).elim
  have howner (c : Fin S.capCount) : S.owner c = i ↔ c = a ∨ c = b := by
    constructor
    · intro hc
      rcases hsig c with hs | hs
      · exact Or.inl (hsame c a hc ha (hs.trans hsigns.1.symm))
      · exact Or.inr (hsame c b hc hb (hs.trans hsigns.2.symm))
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
  have hpositive (c : Fin S.capCount) :
      S.owner c = i ∧ (S.cap c).sign = 1 ↔ c = a := by
    constructor
    · intro hc
      exact hsame c a hc.1 ha (hc.2.trans hsigns.1.symm)
    · rintro rfl
      exact ⟨ha, hsigns.1⟩
  have hnegative (c : Fin S.capCount) :
      S.owner c = i ∧ (S.cap c).sign = -1 ↔ c = b := by
    constructor
    · intro hc
      exact hsame c b hc.1 hb (hc.2.trans hsigns.2.symm)
    · rintro rfl
      exact ⟨hb, hsigns.2⟩
  let f : Fin 2 → {c : Fin S.capCount // S.owner c = i} :=
    fun k => if k = 0 then ⟨a, ha⟩ else ⟨b, hb⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · have he := congrArg Subtype.val hxy
        norm_num [f] at he
        exact (hab he).elim
      · have he := congrArg Subtype.val hxy
        norm_num [f] at he
        exact (hab he.symm).elim
      · rfl
    · rintro ⟨c, hc⟩
      rcases (howner c).mp hc with rfl | rfl
      · exact ⟨0, by norm_num [f]⟩
      · exact ⟨1, by norm_num [f]⟩
  have hcard : Fintype.card {c : Fin S.capCount // S.owner c = i} = 2 := by
    calc
      _ = Fintype.card (Fin 2) := (Fintype.card_congr (Equiv.ofBijective f hbij)).symm
      _ = 2 := Fintype.card_fin 2
  refine ⟨a, b, p, q, z0, ha, hb, hab, hsigns.1, hsigns.2,
    howner, hpositive, hnegative, hcard, hp, hq, hpa, hqb, hmin, hmax,
    hlower a ha hsigns.1, hupper b hb hsigns.2, hha, hhb, ?_⟩
  intro x hx
  constructor
  · rw [← hha p hpa]
    exact hmin hx
  · rw [← hhb q hqb]
    exact hmax hx

end PoincareConjecture.M25.Topology3D
