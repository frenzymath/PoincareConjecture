import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerLocalFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerFillingField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelFlow










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_inner_reference_filling :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    let B : ℝ := 17 / 16 + 1 / 8192
    ∃ (vmin : E2) (m : ℝ) (e : OpenPartialHomeomorph E2 E2),
      m = U vmin ∧ (63 : ℝ) / 64 ≤ m ∧ m ≤ 1 ∧ e 0 = vmin ∧
      e.source = Metric.ball 0 (Real.sqrt (B - m)) ∧
      e.target = {v : E2 | ‖v‖ < 1 / 2 ∧ U v < B} ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.source, U (e p) = m + ‖p‖ ^ 2) ∧
      (∀ b : ℝ, m ≤ b → b < B →
        e '' Metric.closedBall 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
        e '' Metric.ball 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v < b} ∧
        e '' Metric.sphere 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v = b}) := by
  classical
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  let D : Set E2 := ball 0 (1 / 2)
  let B : ℝ := 17 / 16 + 1 / 8192
  obtain ⟨vmin, m, a, e0, hvm, hm, hlo, hhi, hcrit, hgap, ha,
    haB, hzero, hsource, htarget, he, hei, hquad, hfull, _himages⟩ :=
      exists_inner_reference_local_filling
  change m = U vmin at hm
  change m + 9 * a ^ 2 < B at haB
  change ∀ v ∈ Q, m + ‖v - vmin‖ ^ 2 / 6 ≤ U v at hgap
  change ∀ p ∈ e0.source, U (e0 p) = m + ‖p‖ ^ 2 at hquad
  change ∀ v ∈ Q, U v ≤ m + 9 * a ^ 2 → v ∈ e0.target at hfull
  obtain ⟨beta, W, hb, hbc, _hbs, hbOne, _hbrange, hW, hWc, hWs,
      hWheight, hWradial⟩ := exists_inner_reference_filling_field
    vmin m a e0 hm ha haB hzero hsource htarget he hei hquad hfull hcrit
  change ∀ v ∈ D, fderiv ℝ U v (W v) = beta (U v) at hWheight
  obtain ⟨hUs, _, _, _, _, _, v0, _hv0, _hl0, _hh0, _hc0, _hu0,
    _hi0, _hg0, hsub⟩ := inner_reference_convex_geometry
  change ContDiffOn ℝ ∞ U (ball (0 : E2) 1) at hUs
  change ∀ b ≤ (17 : ℝ) / 16 + 2 / 8192,
    IsCompact {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
    {v : E2 | v ∈ Q ∧ U v ≤ b} ⊆ D at hsub
  have hDunit : D ⊆ ball (0 : E2) 1 := by
    intro v hv
    rw [mem_ball_zero_iff] at hv ⊢
    linarith only [hv]
  have hU : ContDiffOn ℝ ∞ U D := hUs.mono hDunit
  have hUc : Continuous U :=
    ((continuous_norm.pow 2).add
      ((continuous_const.sub (continuous_norm.pow 2)).sqrt)).add
        ((EuclideanSpace.proj (0 : Fin 2)).continuous.div_const 32)
  have hmin (v : E2) (hv : v ∈ Q) : m ≤ U v := by
    linarith only [hgap v hv, sq_nonneg ‖v - vmin‖]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hmB : 0 < B - m := by linarith only [haB, ha2]
  let R := Real.sqrt (B - m)
  have hR : 0 < R := Real.sqrt_pos.mpr hmB
  have hR2 : R ^ 2 = B - m := Real.sq_sqrt hmB.le
  let S : Set E2 := ball 0 R
  let Omega : Set E2 := {v : E2 | ‖v‖ < 1 / 2 ∧ U v < B}
  have hOmega : IsOpen Omega :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt hUc continuous_const)
  have hOmD (v : E2) (hv : v ∈ Omega) : v ∈ D := mem_ball_zero_iff.mpr hv.1
  have hOmQ (v : E2) (hv : v ∈ Omega) : v ∈ Q := ball_subset_closedBall (hOmD v hv)
  have hSrc (p : E2) (hp : ‖p‖ ≤ 3 * a) : p ∈ e0.source :=
    hsource (mem_closedBall_zero_iff.mpr hp)
  have hInvQuad (v : E2) (hv : v ∈ e0.target) : U v = m + ‖e0.symm v‖ ^ 2 := by
    simpa only [e0.right_inv hv] using hquad _ (e0.map_target hv)
  obtain ⟨KW, LW, hKW, hLW⟩ := compactField_bounds W hW hWc
  obtain ⟨Kb, Lb, hKb, hLb⟩ := compactField_bounds beta hb hbc
  let Phi : E2 → ℝ → E2 := boundedFlow W hKW hLW
  have hPhi : ContDiff ℝ ∞ (fun p : E2 × ℝ => Phi p.1 p.2) :=
    boundedFlow_contDiff W hKW hLW hW hWc
  have hWzero (v : E2) (hv : v ∉ D) : W v = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hv (hWs h).1)
  have hPhiD (v : E2) (hv : v ∈ D) (t : ℝ) : Phi v t ∈ D :=
    boundedFlow_mapsTo_set W hKW hLW hWzero t hv
  let ell := m + a ^ 2 / 2
  let center := (ell + B) / 2
  let width := (B - ell) / 2
  have hellB : ell < B :=
    (show ell < m + 9 * a ^ 2 by dsimp only [ell]; linarith only [ha2]).trans haB
  have hwidth : 0 < width := div_pos (sub_pos.mpr hellB) (by norm_num)
  have hfromCenter (b : ℝ) (hbI : b ∈ Ioo ell B) :
      boundedFlow beta hKb hLb center (b - center) = b := by
    have hh := scalarFlow_eq_add_on beta hKb hLb center hwidth (by
      intro z hz
      apply hbOne
      dsimp only [center, width, ell, B] at hz ⊢
      constructor <;> linarith only [hz.1, hz.2]) (t := b - center) (by
      dsimp only [center, width, ell, B] at hbI ⊢
      constructor <;> linarith only [hbI.1, hbI.2])
    simpa only [add_sub_cancel] using hh
  have hscalar (b c : ℝ) (hbI : b ∈ Ioo ell B) (hcI : c ∈ Ioo ell B) :
      boundedFlow beta hKb hLb b (c - b) = c := by
    calc
      _ = boundedFlow beta hKb hLb
          (boundedFlow beta hKb hLb center (b - center)) (c - b) := by
        rw [hfromCenter b hbI]
      _ = boundedFlow beta hKb hLb center (c - center) := by
        rw [← boundedFlow_add]
        congr 1
        ring
      _ = c := hfromCenter c hcI
  have hheight (v : E2) (hv : v ∈ D) (b : ℝ)
      (hvI : U v ∈ Ioo ell B) (hbI : b ∈ Ioo ell B) :
      U (Phi v (b - U v)) = b := by
    rw [boundedFlow_intertwines_on W hKW hLW beta hKb hLb U
      (fun x hx => (hU.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      hWheight v (hPhiD v hv)]
    exact hscalar (U v) b hvI hbI
  have hbaseI : m + a ^ 2 ∈ Ioo ell B := by
    dsimp only [ell]
    constructor <;> linarith only [haB, ha2]
  have hlocal (q : E2) (hq : ‖q‖ = 1) :
      EqOn (Phi (e0 (a • q)))
        (fun t : ℝ => e0 (Real.sqrt (a ^ 2 + t) • q)) (Ioo (-a ^ 2 / 2) (a ^ 2)) := by
    have hzeroI : (0 : ℝ) ∈ Ioo (-a ^ 2 / 2) (a ^ 2) := by
      constructor <;> linarith only [ha2]
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => W) (s := fun _ => univ)
      (fun _ _ => hKW.lipschitzOnWith) hzeroI
    · exact fun t _ => ⟨boundedFlow_hasDerivAt W hKW hLW _ t, mem_univ _⟩
    · intro t ht
      have hrad : 0 < a ^ 2 + t := by linarith only [ht.1, ha2]
      have hn : ‖Real.sqrt (a ^ 2 + t) • q‖ = Real.sqrt (a ^ 2 + t) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hq, mul_one]
      have hn2 : ‖Real.sqrt (a ^ 2 + t) • q‖ ^ 2 = a ^ 2 + t := by
        rw [hn, Real.sq_sqrt hrad.le]
      have hp : Real.sqrt (a ^ 2 + t) • q ∈ e0.source := by
        apply hSrc
        nlinarith only [hn2, ht.2, ha, norm_nonneg (Real.sqrt (a ^ 2 + t) • q)]
      refine ⟨?_, mem_univ _⟩
      rw [hWradial _ (by rw [hn2]; linarith only [ht.1])
        (by rw [hn2]; linarith only [ht.2])]
      have htrack := (((hasDerivAt_id t).const_add (a ^ 2)).sqrt hrad.ne').smul_const q
      have hetrack := ((he.contDiffAt (e0.open_source.mem_nhds hp)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt t htrack
      have hs := Real.sq_sqrt hrad.le
      have hs0 := (Real.sqrt_pos.mpr hrad).ne'
      have hc : (2 * (a ^ 2 + t))⁻¹ * Real.sqrt (a ^ 2 + t) =
          1 / (2 * Real.sqrt (a ^ 2 + t)) := by
        rw [inv_mul_eq_div]
        apply (div_eq_div_iff (mul_ne_zero (by norm_num) hrad.ne')
          (mul_ne_zero (by norm_num) hs0)).2
        nlinarith only [hs]
      have hvder : (2 * ‖Real.sqrt (a ^ 2 + t) • q‖ ^ 2)⁻¹ •
          (Real.sqrt (a ^ 2 + t) • q) =
          (1 / (2 * Real.sqrt (a ^ 2 + t))) • q := by
        rw [hn2, smul_smul, hc]
      rw [hvder]
      exact hetrack
    · dsimp only [Phi]
      rw [boundedFlow_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  let anchor : E2 → E2 := fun p => (a / ‖p‖) • p
  have hanchorNorm (p : E2) (hp : p ≠ 0) : ‖anchor p‖ = a := by
    dsimp only [anchor]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha (norm_pos_iff.mpr hp)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hp)]
  have hanchorS (p : E2) (hp : p ≠ 0) : anchor p ∈ e0.source :=
    hSrc _ (by rw [hanchorNorm p hp]; linarith only [ha])
  have hanchorU (p : E2) (hp : p ≠ 0) : U (e0 (anchor p)) = m + a ^ 2 := by
    rw [hquad _ (hanchorS p hp), hanchorNorm p hp]
  let outer : E2 → E2 := fun p => Phi (e0 (anchor p)) (‖p‖ ^ 2 - a ^ 2)
  have houterLocal (p : E2) (hloP : a ^ 2 / 2 < ‖p‖ ^ 2)
      (hhiP : ‖p‖ ^ 2 < 2 * a ^ 2) : outer p = e0 p := by
    have hp : p ≠ 0 := by
      intro hz
      norm_num only [hz, norm_zero] at hloP
      linarith only [hloP, ha2]
    have hq : ‖(‖p‖)⁻¹ • p‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hp),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]
    have hh := hlocal ((‖p‖)⁻¹ • p) hq (by
      constructor <;> linarith only [hloP, hhiP] :
        ‖p‖ ^ 2 - a ^ 2 ∈ Ioo (-a ^ 2 / 2) (a ^ 2))
    have hsq : Real.sqrt (a ^ 2 + (‖p‖ ^ 2 - a ^ 2)) = ‖p‖ := by
      rw [show a ^ 2 + (‖p‖ ^ 2 - a ^ 2) = ‖p‖ ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg p)]
    simpa only [outer, anchor, smul_smul, div_eq_mul_inv, hsq,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_smul] using hh
  let f : E2 → E2 := fun p => if ‖p‖ ≤ a then e0 p else outer p
  have hfLocal (p : E2) (hp : ‖p‖ ^ 2 < 2 * a ^ 2) : f p = e0 p := by
    dsimp only [f]
    split_ifs with hpa
    · rfl
    · exact houterLocal p (by nlinarith only [lt_of_not_ge hpa, ha]) hp
  have hfMap (p : E2) (hp : p ∈ S) : f p ∈ Omega ∧ U (f p) = m + ‖p‖ ^ 2 := by
    have hpnorm : ‖p‖ < R := mem_ball_zero_iff.mp hp
    have hpheight : m + ‖p‖ ^ 2 < B := by nlinarith only [hpnorm, hR2, norm_nonneg p, hR]
    by_cases hpa : ‖p‖ ≤ a
    · have hpS := hSrc p (by linarith only [hpa, ha])
      rw [show f p = e0 p by simp only [f, if_pos hpa]]
      exact ⟨⟨mem_ball_zero_iff.mp (htarget (e0.map_source hpS)),
        (hquad p hpS).trans_lt hpheight⟩, hquad p hpS⟩
    · have hpa' : a < ‖p‖ := lt_of_not_ge hpa
      have hp0 : p ≠ 0 := norm_pos_iff.mp (ha.trans hpa')
      have hxD := htarget (e0.map_source (hanchorS p hp0))
      have hval : U (outer p) = m + ‖p‖ ^ 2 := by
        have hh := hheight (e0 (anchor p)) hxD (m + ‖p‖ ^ 2)
          (by rw [hanchorU p hp0]; exact hbaseI)
          ⟨by dsimp only [ell]; nlinarith only [hpa', ha], hpheight⟩
        simpa only [outer, hanchorU p hp0, add_sub_add_left_eq_sub] using hh
      rw [show f p = outer p by simp only [f, if_neg hpa]]
      exact ⟨⟨mem_ball_zero_iff.mp (hPhiD _ hxD _), hval.trans_lt hpheight⟩, hval⟩
  let back : E2 → E2 := fun v => Phi v (a ^ 2 - (U v - m))
  have hBack (v : E2) (hv : v ∈ Omega) (hvhi : m + a ^ 2 < U v) :
      back v ∈ e0.target ∧ U (back v) = m + a ^ 2 ∧ ‖e0.symm (back v)‖ = a := by
    have hvI : U v ∈ Ioo ell B :=
      ⟨by dsimp only [ell]; linarith only [hvhi, ha2], hv.2⟩
    have hval : U (back v) = m + a ^ 2 := by
      convert hheight v (hOmD v hv) (m + a ^ 2) hvI hbaseI using 1
      simp only [back]
      congr 2
      ring
    have hbD : back v ∈ D := hPhiD v (hOmD v hv) _
    have hbT : back v ∈ e0.target := hfull _ (ball_subset_closedBall hbD)
      (by rw [hval]; linarith only [ha2])
    refine ⟨hbT, hval, ?_⟩
    have hh := hInvQuad _ hbT
    nlinarith only [hh, hval, norm_nonneg (e0.symm (back v)), ha]
  let invOuter : E2 → E2 := fun v =>
    (Real.sqrt (U v - m) / a) • e0.symm (back v)
  have hInvNorm (v : E2) (hv : v ∈ Omega) (hvhi : m + a ^ 2 < U v) :
      ‖invOuter v‖ = Real.sqrt (U v - m) := by
    dsimp only [invOuter]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) ha.le), (hBack v hv hvhi).2.2,
      div_mul_cancel₀ _ ha.ne']
  have hInvAnchor (v : E2) (hv : v ∈ Omega) (hvhi : m + a ^ 2 < U v) :
      anchor (invOuter v) = e0.symm (back v) := by
    have hr : Real.sqrt (U v - m) ≠ 0 := (Real.sqrt_pos.mpr
      (by linarith only [hvhi, ha2])).ne'
    change (a / ‖invOuter v‖) • ((Real.sqrt (U v - m) / a) • e0.symm (back v)) = _
    rw [hInvNorm v hv hvhi, smul_smul]
    have hc : a / Real.sqrt (U v - m) * (Real.sqrt (U v - m) / a) = 1 := by
      field_simp
    rw [hc, one_smul]
  let g : E2 → E2 := fun v => if U v ≤ m + a ^ 2 then e0.symm v else invOuter v
  have hgMap (v : E2) (hv : v ∈ Omega) : g v ∈ S ∧ f (g v) = v := by
    by_cases hvlo : U v ≤ m + a ^ 2
    · have hvT : v ∈ e0.target := hfull v (hOmQ v hv)
        (by linarith only [hvlo, ha2])
      have hval := hInvQuad v hvT
      have hpA : ‖e0.symm v‖ ≤ a := by
        nlinarith only [hval, hvlo, norm_nonneg (e0.symm v), ha]
      have hpR : ‖e0.symm v‖ < R := by
        nlinarith only [hval, hv.2, hR2, hR, norm_nonneg (e0.symm v)]
      rw [show g v = e0.symm v by simp only [g, if_pos hvlo]]
      exact ⟨mem_ball_zero_iff.mpr hpR, by
        dsimp only [f]
        rw [if_pos hpA, e0.right_inv hvT]⟩
    · have hvhi : m + a ^ 2 < U v := lt_of_not_ge hvlo
      have hr0 : 0 < U v - m := by linarith only [hvhi, ha2]
      have hrsq := Real.sq_sqrt hr0.le
      have hrpos := Real.sqrt_pos.mpr hr0
      have hrA : a < Real.sqrt (U v - m) := by nlinarith only [hrsq, hvhi, ha, hrpos]
      have hrR : Real.sqrt (U v - m) < R := by nlinarith only [hrsq, hR2, hv.2, hrpos, hR]
      rw [show g v = invOuter v by simp only [g, if_neg hvlo]]
      refine ⟨mem_ball_zero_iff.mpr (by rw [hInvNorm v hv hvhi]; exact hrR), ?_⟩
      dsimp only [f]
      rw [if_neg (by rw [hInvNorm v hv hvhi]; exact not_le.mpr hrA)]
      dsimp only [outer]
      rw [
        hInvAnchor v hv hvhi, e0.right_inv (hBack v hv hvhi).1, hInvNorm v hv hvhi, hrsq]
      change Phi (Phi v (a ^ 2 - (U v - m))) (U v - m - a ^ 2) = v
      rw [show U v - m - a ^ 2 = -(a ^ 2 - (U v - m)) by ring]
      exact boundedFlow_neg W hKW hLW v _
  have hgf (p : E2) (hp : p ∈ S) : g (f p) = p := by
    have hfp := hfMap p hp
    by_cases hpa : ‖p‖ ≤ a
    · have hpS := hSrc p (by linarith only [hpa, ha])
      have hfEq : f p = e0 p := by simp only [f, if_pos hpa]
      have hval : U (f p) ≤ m + a ^ 2 := by
        rw [hfp.2]
        nlinarith only [hpa, norm_nonneg p, ha]
      dsimp only [g]
      rw [if_pos hval, hfEq, e0.left_inv hpS]
    · have hpa' : a < ‖p‖ := lt_of_not_ge hpa
      have hp0 : p ≠ 0 := norm_pos_iff.mp (ha.trans hpa')
      have hval : m + a ^ 2 < U (f p) := by
        rw [hfp.2]
        nlinarith only [hpa', ha]
      have hfEq : f p = outer p := by simp only [f, if_neg hpa]
      have hbEq : back (f p) = e0 (anchor p) := by
        change Phi (f p) (a ^ 2 - (U (f p) - m)) = _
        rw [hfp.2, add_sub_cancel_left, hfEq]
        dsimp only [outer]
        rw [show a ^ 2 - ‖p‖ ^ 2 = -(‖p‖ ^ 2 - a ^ 2) by ring]
        exact boundedFlow_neg W hKW hLW _ _
      dsimp only [g]
      rw [if_neg (not_le.mpr hval)]
      dsimp only [invOuter]
      rw [hbEq, e0.left_inv (hanchorS p hp0),
        hfp.2, add_sub_cancel_left, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg p)]
      change (‖p‖ / a) • ((a / ‖p‖) • p) = p
      rw [smul_smul]
      have hc : ‖p‖ / a * (a / ‖p‖) = 1 := by field_simp
      rw [hc, one_smul]
  have hgLocal (v : E2) (hv : v ∈ Omega) (hvlo : U v < m + 2 * a ^ 2) :
      g v = e0.symm v := by
    have hvT : v ∈ e0.target := hfull v (hOmQ v hv)
      (by linarith only [hvlo, ha2])
    have hval := hInvQuad v hvT
    have hpS : e0.symm v ∈ S := mem_ball_zero_iff.mpr (by
      nlinarith only [hval, hv.2, hR2, hR, norm_nonneg (e0.symm v)])
    have hfEq : f (e0.symm v) = v := by
      rw [hfLocal _ (by linarith only [hval, hvlo]), e0.right_inv hvT]
    simpa only [hfEq] using hgf _ hpS
  have hf : ContDiffOn ℝ ∞ f S := by
    intro p _hp
    by_cases hloP : ‖p‖ ^ 2 < 2 * a ^ 2
    · have hpS : p ∈ e0.source := hSrc p (by
        nlinarith only [hloP, ha, norm_nonneg p])
      have heq : f =ᶠ[𝓝 p] e0 := by
        filter_upwards [(isOpen_lt (continuous_norm.pow 2) continuous_const).mem_nhds hloP]
          with y hy
        exact hfLocal y hy
      exact ((he.contDiffAt (e0.open_source.mem_nhds hpS)).congr_of_eventuallyEq
        heq).contDiffWithinAt
    · have hpa : a < ‖p‖ := by nlinarith only [le_of_not_gt hloP, ha, norm_nonneg p]
      have hp0 : p ≠ 0 := norm_pos_iff.mp (ha.trans hpa)
      have hanchor : ContDiffAt ℝ ∞ anchor p :=
        (contDiffAt_const.div (contDiffAt_id.norm ℝ hp0)
          (norm_ne_zero_iff.mpr hp0)).smul contDiffAt_id
      have ho : ContDiffAt ℝ ∞ outer p := hPhi.contDiffAt.comp p
        ((((he.contDiffAt (e0.open_source.mem_nhds (hanchorS p hp0))).comp p hanchor).prodMk
          ((contDiffAt_id.norm_sq ℝ).sub contDiffAt_const)))
      have heq : f =ᶠ[𝓝 p] outer := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hpa] with y hy
        exact if_neg (not_le.mpr hy)
      exact (ho.congr_of_eventuallyEq heq).contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ g Omega := by
    intro v hv
    have hvD : v ∈ D := hOmD v hv
    have hUv : ContDiffAt ℝ ∞ U v := hU.contDiffAt (isOpen_ball.mem_nhds hvD)
    by_cases hvlo : U v < m + 2 * a ^ 2
    · have hvT : v ∈ e0.target := hfull v (hOmQ v hv)
        (by linarith only [hvlo, ha2])
      have heq : g =ᶠ[𝓝 v] e0.symm := by
        filter_upwards [hOmega.mem_nhds hv,
          (isOpen_lt hUc continuous_const).mem_nhds hvlo] with y hy hylo
        exact hgLocal y hy hylo
      exact ((hei.contDiffAt (e0.open_target.mem_nhds hvT)).congr_of_eventuallyEq
        heq).contDiffWithinAt
    · have hvhi : m + a ^ 2 < U v := by linarith only [le_of_not_gt hvlo, ha2]
      have hr0 : U v - m ≠ 0 := ne_of_gt (by linarith only [hvhi, ha2])
      have hbv : ContDiffAt ℝ ∞ back v := hPhi.contDiffAt.comp v
        (contDiffAt_id.prodMk (contDiffAt_const.sub (hUv.sub contDiffAt_const)))
      have ho : ContDiffAt ℝ ∞ invOuter v :=
        (((hUv.sub contDiffAt_const).sqrt hr0).div_const a).smul
          ((hei.contDiffAt (e0.open_target.mem_nhds (hBack v hv hvhi).1)).comp v hbv)
      have heq : g =ᶠ[𝓝 v] invOuter := by
        filter_upwards [(isOpen_lt continuous_const hUc).mem_nhds hvhi] with y hy
        exact if_neg (not_le.mpr hy)
      exact (ho.congr_of_eventuallyEq heq).contDiffWithinAt
  let e : OpenPartialHomeomorph E2 E2 :=
    { toFun := f
      invFun := g
      source := S
      target := Omega
      map_source' := fun p hp => (hfMap p hp).1
      map_target' := fun v hv => (hgMap v hv).1
      left_inv' := hgf
      right_inv' := fun v hv => (hgMap v hv).2
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn
      open_source := isOpen_ball
      open_target := hOmega }
  have heZero : e 0 = vmin := by
    change f 0 = vmin
    rw [hfLocal 0 (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) ha2), hzero]
  refine ⟨vmin, m, e, hm, hlo, hhi, heZero, rfl, rfl, hf, hg,
    (fun p hp => (hfMap p hp).2), ?_⟩
  intro b hmb hbB
  change b < B at hbB
  change e '' closedBall 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
    e '' ball 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v < b} ∧
    e '' sphere 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v = b}
  have hbnonneg : 0 ≤ b - m := sub_nonneg.mpr hmb
  have hbSq := Real.sq_sqrt hbnonneg
  have hbr0 := Real.sqrt_nonneg (b - m)
  have hbrR : Real.sqrt (b - m) < R := by nlinarith only [hbSq, hR2, hbB, hbr0, hR]
  have hsmallS (p : E2) (hp : p ∈ closedBall (0 : E2) (Real.sqrt (b - m))) : p ∈ S :=
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt hbrR)
  have hTarget (v : E2) (hv : v ∈ Q) (hvval : U v ≤ b) : v ∈ Omega := by
    have hbBig : b ≤ (17 : ℝ) / 16 + 2 / 8192 := by dsimp only [B] at hbB; linarith only [hbB]
    exact ⟨mem_ball_zero_iff.mp ((hsub b hbBig).2 ⟨hv, hvval⟩), hvval.trans_lt hbB⟩
  have hreverse (v : E2) (hv : v ∈ Omega) : U v = m + ‖e.symm v‖ ^ 2 := by
    have hh := (hfMap (g v) (hgMap v hv).1).2
    rw [(hgMap v hv).2] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hh := hfMap p (hsmallS p hp)
      refine ⟨hOmQ _ hh.1, ?_⟩
      change U (f p) ≤ b
      rw [hh.2]
      nlinarith only [mem_closedBall_zero_iff.mp hp, hbSq, hbr0, norm_nonneg p]
    · rintro ⟨hv, hvval⟩
      have hvT := hTarget v hv hvval
      refine ⟨e.symm v, mem_closedBall_zero_iff.mpr ?_, e.right_inv hvT⟩
      nlinarith only [hreverse v hvT, hvval, hbSq, hbr0, norm_nonneg (e.symm v)]
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hh := hfMap p (hsmallS p (ball_subset_closedBall hp))
      refine ⟨hOmQ _ hh.1, ?_⟩
      change U (f p) < b
      rw [hh.2]
      nlinarith only [mem_ball_zero_iff.mp hp, hbSq, hbr0, norm_nonneg p]
    · rintro ⟨hv, hvval⟩
      have hvT := hTarget v hv hvval.le
      refine ⟨e.symm v, mem_ball_zero_iff.mpr ?_, e.right_inv hvT⟩
      nlinarith only [hreverse v hvT, hvval, hbSq, hbr0, norm_nonneg (e.symm v)]
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hh := hfMap p (hsmallS p (sphere_subset_closedBall hp))
      refine ⟨hOmQ _ hh.1, ?_⟩
      change U (f p) = b
      rw [hh.2, mem_sphere_zero_iff_norm.mp hp]
      linarith only [hbSq]
    · rintro ⟨hv, hvval⟩
      have hvT := hTarget v hv hvval.le
      refine ⟨e.symm v, mem_sphere_zero_iff_norm.mpr ?_, e.right_inv hvT⟩
      nlinarith only [hreverse v hvT, hvval, hbSq, hbr0, norm_nonneg (e.symm v)]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
