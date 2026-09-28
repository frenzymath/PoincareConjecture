import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessNormalGraphFamily
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessSmoothReference
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessGraphNeighborhood
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessNormalLabels
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessInterval











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ} {F : RicciFlow n M (Icc a b)}

local notation "W" => EuclideanSpace ℝ ι
local notation "G" => ℝ × (W × W)





theorem exists_forward_c2ShrinkingCurve_agreement
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {N : Set W} (hN : IsOpen N) (heN : range e ⊆ N) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ N) (hret : ∀ p, ρ (e p) = p)
    {s T : ℝ} (hsT : s < T) {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    (hd : M63C2ShrinkingCurveOn F d (Icc s T))
    (hinit : ∀ x, c x s = d x s) :
    ∃ tau : ℝ, s < tau ∧ tau ≤ T ∧ ∀ t ∈ Icc s tau, ∀ x, c x t = d x t := by
  classical
  have heinj : Function.Injective e := (show Function.LeftInverse ρ e from hret).injective
  have hs : s ∈ Icc s T := ⟨le_rfl, hsT.le⟩
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hbase := c2ShrinkingCurve_embedded_closed_data hc he
  have himm (x : ℝ) : deriv (fun y => e (c y s)) x ≠ 0 := by
    intro hx
    have hv := (hbase.2.1 s hs x).deriv
    have hzero : mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x s)
        (curveVelocity (n := n) (fun y => c y s) x) = 0 := hv.symm.trans hx
    have hleft := (smooth_retraction_differentials he hN heN hρ hret).2.2
      (c x s) (curveVelocity (n := n) (fun y => c y s) x)
    rw [hzero, map_zero] at hleft
    exact hc.immersed s hs x hleft.symm
  have hperiod : Function.Periodic (fun x => e (c x s)) curvePeriod :=
    fun x => congrArg e (hc.periodic s hs x)
  obtain ⟨r, m, M0, B0, radius, eps, eta, hr, hrper, hm, hM0, hB0,
    hradius, heps, heta, hlower, hupper, hsecond, hsmall, hmargin, htrans,
    hclose0, hfirst0⟩ :=
    exists_periodic_smooth_normalGraph_reference hP (hbase.1 s hs) hperiod himm
  let C : Bool → ℝ → ℝ → M := Bool.rec c d
  have hC (i : Bool) : M63C2ShrinkingCurveOn F (C i) (Icc s T) := by
    cases i
    · exact hc
    · exact hd
  have hCinit (i : Bool) : (fun x => e (C i x s)) = (fun x => e (c x s)) := by
    funext x
    cases i
    · rfl
    · exact congrArg e (hinit x).symm
  have hnear (i : Bool) := exists_c2ShrinkingCurve_embedded_C1_neighborhood (hC i) he
    (hr.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hrper hsT (Subset.refl _) heps heta
    (fun x => by
      change ‖(fun y => e (C i y s)) x - r x‖ < eps
      rw [hCinit i]
      exact (hclose0 x).trans (half_lt_self heps))
    (fun x => by
      rw [hCinit i]
      exact (hfirst0 x).trans (half_lt_self heta))
  choose terminal hterminal hterminalT hnearbound using hnear
  let tau := min (terminal false) (terminal true)
  have hstau : s < tau := lt_min (hterminal false) (hterminal true)
  have htauterminal (i : Bool) : tau ≤ terminal i := by
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have htauT : tau ≤ T := (htauterminal false).trans (hterminalT false)
  have hCshort (i : Bool) : M63C2ShrinkingCurveOn F (C i) (Icc s tau) :=
    c2_restrict (hC i) (fun _ ht => ⟨ht.1, ht.2.trans htauT⟩)
  have hclose (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      ‖e (C i x t) - r x‖ < eps :=
    (hnearbound i t ⟨ht.1, ht.2.trans (htauterminal i)⟩ x).1
  have hfirst (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      ‖deriv (fun y => e (C i y t)) x - deriv r x‖ ≤ eta :=
    (hnearbound i t ⟨ht.1, ht.2.trans (htauterminal i)⟩ x).2.le
  have hgraphs (i : Bool) := exists_c2ShrinkingCurve_normalGraph_family
    he hN heN hρ hret hstau (hCshort i) hr hm hM0 hB0.le hradius heps
      hlower hupper hsecond hsmall hmargin heta.le htrans hrper (hclose i) (hfirst i)
  choose phi hdata hfamily using hgraphs
  let psi : Bool → ℝ → ℝ → ℝ := fun i y t => (phi i t).symm y
  let U : Bool → ℝ → ℝ → W := fun i y t => e (C i (psi i y t) t) - r y
  let P : Bool → ℝ → ℝ → W := fun i y t => deriv (fun z => U i z t) y
  let Q : Bool → ℝ → ℝ → W := fun i y t => deriv (deriv (fun z => U i z t)) y
  let V : Bool → ℝ → ℝ → W := fun i y t => deriv (fun z => e (C i (psi i z t) t)) y
  let A : Bool → ℝ → ℝ → ℝ := fun i y t =>
    ambientCurvePrincipal F ρ t (r y + U i y t) (deriv r y + P i y t)
  let B : Bool → ℝ → ℝ → W := fun i y t => curveGraphLower (A i y t)
    (ambientCurveLower F e ρ t (r y + U i y t) (deriv r y + P i y t))
    (deriv r y) (deriv (deriv r) y) (deriv (deriv (deriv r)) y) (U i y t) (P i y t)
  let D : Set (ℝ × ℝ) := univ ×ˢ Icc s tau
  have hPhiC2 (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) :
      ContDiff ℝ 2 (phi i t : ℝ → ℝ) := (hdata i t ht).2.1
  have hPsiC2 (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) :
      ContDiff ℝ 2 (fun y => psi i y t) := (hdata i t ht).2.2.1
  have hPhiPos (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      0 < deriv (phi i t) x := (hdata i t ht).2.2.2.2.1 x
  have hPsiPos (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      0 < deriv (fun y => psi i y t) x := ((hdata i t ht).2.2.2.2.2.1 x).2
  have hUC2 (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) :
      ContDiff ℝ 2 (fun y => U i y t) := (hdata i t ht).2.2.2.2.2.2.2.2.1
  have hUper (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      U i (x + curvePeriod) t = U i x t := (hdata i t ht).2.2.2.2.2.2.2.2.2.1 x
  have hPsiCont (i : Bool) : ContinuousOn (Function.uncurry (psi i)) D := (hfamily i).1
  have hPsiC1 (i : Bool) : ContDiffOn ℝ 1 (Function.uncurry (psi i))
      (univ ×ˢ Ioo s tau) := (hfamily i).2.2.1
  have hUCont (i : Bool) : ContinuousOn (Function.uncurry (U i)) D :=
    (hfamily i).2.2.2.1
  have hPCont (i : Bool) : ContinuousOn (Function.uncurry (P i)) D :=
    (hfamily i).2.2.2.2.1
  have hQCont (i : Bool) : ContinuousOn (Function.uncurry (Q i)) D :=
    (hfamily i).2.2.2.2.2.1
  have hpoint (i : Bool) (y t : ℝ) : r y + U i y t = e (C i (psi i y t) t) := by
    dsimp only [U]
    abel
  have hV (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (y : ℝ) :
      V i y t = deriv r y + P i y t := by
    have hsp := (c2ShrinkingCurve_embedded_closed_data (hCshort i) he).1 t ht
    have hdiff := (hsp.comp (hPsiC2 i t ht)).differentiable (by norm_num)
    have hder := deriv_sub (hdiff y) (hr.differentiable (by simp) y)
    change P i y t = V i y t - deriv r y at hder
    rw [hder]
    abel
  have htime (i : Bool) (t : ℝ) (ht : t ∈ Ioo s tau) (y : ℝ) :
      HasDerivAt (U i y) (A i y t • Q i y t + B i y t) t := by
    have hdtime := (hfamily i).2.2.2.2.2.2.2.2 t ht y
    change HasDerivAt (U i y)
      (ambientCurvePrincipal F ρ t (e (C i (psi i y t) t)) (V i y t) • Q i y t +
        curveGraphLower (ambientCurvePrincipal F ρ t (e (C i (psi i y t) t)) (V i y t))
          (ambientCurveLower F e ρ t (e (C i (psi i y t) t)) (V i y t))
          (deriv r y) (deriv (deriv r) y) (deriv (deriv (deriv r)) y)
          (U i y t) (P i y t)) t at hdtime
    rw [hV i t (Ioo_subset_Icc_self ht) y, ← hpoint i y t] at hdtime
    exact hdtime
  let Ω : Set G := {z | r z.1 + z.2.1 ∈ N ∧
    mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
    ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}
  let state : Bool → ℝ × ℝ → G := fun i z => (z.1, U i z.1 z.2, P i z.1 z.2)
  have hstate (i : Bool) (z : ℝ × ℝ) (hz : z ∈ D) : state i z ∈ Ω := by
    have hg := (hfamily i).2.2.2.2.2.2.2.1 z.2 hz.2 z.1
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (C i (psi i z.1 z.2) z.2)) (V i z.1 z.2) ≠ 0 ∧
      ⟪V i z.1 z.2, deriv r z.1⟫ ≠ 0 at hg
    rw [hV i z.2 hz.2 z.1, ← hpoint i z.1 z.2] at hg
    exact ⟨by rw [hpoint]; exact heN (mem_range_self _), hg⟩
  let rectangle : Set (ℝ × ℝ) := Icc 0 curvePeriod ×ˢ Icc s tau
  have hrectangle : IsCompact rectangle := isCompact_Icc.prod isCompact_Icc
  have hrectD : rectangle ⊆ D := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hstateCont (i : Bool) : ContinuousOn (state i) rectangle :=
    continuousOn_fst.prodMk (((hUCont i).mono hrectD).prodMk ((hPCont i).mono hrectD))
  let K : Set G := state false '' rectangle ∪ state true '' rectangle
  have hK : IsCompact K :=
    (hrectangle.image_of_continuousOn (hstateCont false)).union
      (hrectangle.image_of_continuousOn (hstateCont true))
  have hKsub : K ⊆ Ω := by
    rintro z (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact hstate false w (hrectD hw)
    · exact hstate true w (hrectD hw)
  obtain ⟨mu, _Lambda, hmu, _hLambda, LA, LB, hcoeff, hLA, hLB⟩ :=
    curveGraphCoefficients_uniform_bounds F he hN hρ hr hK hKsub
  obtain ⟨R0, hR0⟩ := hrectangle.exists_bound_of_continuousOn ((hQCont true).mono hrectD)
  let R := max R0 0
  let L : ℝ := (LA : ℝ) + (LB : ℝ)
  have hR : 0 ≤ R := le_max_right _ _
  have hL : 0 ≤ L := add_nonneg LA.coe_nonneg LB.coe_nonneg
  have hL_A : (LA : ℝ) ≤ L := le_add_of_nonneg_right LB.coe_nonneg
  have hL_B : (LB : ℝ) ≤ L := le_add_of_nonneg_left LA.coe_nonneg
  have hcompact (y t : ℝ) (hy : y ∈ Icc 0 curvePeriod) (ht : t ∈ Icc s tau) :
      mu ≤ A false y t ∧ ‖Q true y t‖ ≤ R ∧
      |A false y t - A true y t| ≤
        L * (‖U false y t - U true y t‖ + ‖P false y t - P true y t‖) ∧
      ‖B false y t - B true y t‖ ≤
        L * (‖U false y t - U true y t‖ + ‖P false y t - P true y t‖) := by
    have htF := (hCshort false).domain_subset ht
    have hfalse : state false (y, t) ∈ K := Or.inl ⟨(y, t), ⟨hy, ht⟩, rfl⟩
    have htrue : state true (y, t) ∈ K := Or.inr ⟨(y, t), ⟨hy, ht⟩, rfl⟩
    have hdist : dist (state false (y, t)) (state true (y, t)) ≤
        ‖U false y t - U true y t‖ + ‖P false y t - P true y t‖ := by
      change max (dist y y) (max (dist (U false y t) (U true y t))
        (dist (P false y t) (P true y t))) ≤ _
      rw [dist_self, max_eq_right (le_max_of_le_left dist_nonneg)]
      rw [dist_eq_norm, dist_eq_norm]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    refine ⟨(hcoeff t htF _ hfalse).1, (hR0 (y, t) ⟨hy, ht⟩).trans (le_max_left _ _), ?_, ?_⟩
    · have hh := (hLA t htF).dist_le_mul _ hfalse _ htrue
      change dist (A false y t) (A true y t) ≤ (LA : ℝ) *
        dist (state false (y, t)) (state true (y, t)) at hh
      rw [Real.dist_eq] at hh
      exact hh.trans (mul_le_mul hL_A hdist dist_nonneg hL)
    · have hh := (hLB t htF).dist_le_mul _ hfalse _ htrue
      change dist (B false y t) (B true y t) ≤ (LB : ℝ) *
        dist (state false (y, t)) (state true (y, t)) at hh
      rw [dist_eq_norm] at hh
      exact hh.trans (mul_le_mul hL_B hdist dist_nonneg hL)
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).2
  have hr₂ := (contDiff_infty_iff_deriv.mp hr₁).2
  have hrper₁ := hrper.deriv_of_differentiable (hr.differentiable (by simp))
  have hrper₂ := hrper₁.deriv_of_differentiable (hr₁.differentiable (by simp))
  have hrper₃ := hrper₂.deriv_of_differentiable (hr₂.differentiable (by simp))
  have hPper (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      P i (x + curvePeriod) t = P i x t :=
    (Function.Periodic.deriv_of_differentiable (f := fun y => U i y t) (hUper i t ht)
      ((hUC2 i t ht).differentiable (by norm_num))) x
  have hQper (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      Q i (x + curvePeriod) t = Q i x t :=
    (Function.Periodic.deriv_of_differentiable (f := fun y => P i y t) (hPper i t ht)
      (hUC2 i t ht).differentiable_deriv_two) x
  have hAper (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      A i (x + curvePeriod) t = A i x t := by
    dsimp only [A]
    rw [hrper x, hrper₁ x, hUper i t ht x, hPper i t ht x]
  have hBper (i : Bool) (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) :
      B i (x + curvePeriod) t = B i x t := by
    dsimp only [B]
    rw [hAper i t ht x, hrper x, hrper₁ x, hrper₂ x, hrper₃ x,
      hUper i t ht x, hPper i t ht x]
  have hbounds (x t : ℝ) (ht : t ∈ Icc s tau) :
      mu ≤ A false x t ∧ ‖Q true x t‖ ≤ R ∧
      |A false x t - A true x t| ≤
        L * (‖U false x t - U true x t‖ + ‖P false x t - P true x t‖) ∧
      ‖B false x t - B true x t‖ ≤
        L * (‖U false x t - U true x t‖ + ‖P false x t - P true x t‖) := by
    let tuple := fun y => (U false y t, U true y t, P false y t, P true y t,
      Q true y t, A false y t, A true y t, B false y t, B true y t)
    have htuple : Function.Periodic tuple curvePeriod := by
      intro y
      dsimp only [tuple]
      rw [hUper false t ht y, hUper true t ht y, hPper false t ht y, hPper true t ht y,
        hQper true t ht y, hAper false t ht y, hAper true t ht y,
        hBper false t ht y, hBper true t ht y]
    obtain ⟨y, hy, heq⟩ := htuple.exists_mem_Ico₀ hP x
    dsimp only [tuple] at heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hu0, hu1, hp0, hp1, hq1, ha0, ha1, hb0, hb1⟩
    rw [hu0, hu1, hp0, hp1, hq1, ha0, ha1, hb0, hb1]
    exact hcompact y t ⟨hy.1, hy.2.le⟩ ht
  have hs' : s ∈ Icc s tau := ⟨le_rfl, hstau.le⟩
  have hphis : phi false s = phi true s := by
    ext x
    calc
      phi false s x = selectedCurveFootpoint r radius eps (x, e (c x s)) :=
        (hdata false s hs').1 x
      _ = selectedCurveFootpoint r radius eps (x, e (d x s)) := by rw [hinit x]
      _ = phi true s x := ((hdata true s hs').1 x).symm
  have hUinit (x : ℝ) : U false x s = U true x s := by
    dsimp only [U, psi]
    rw [hphis]
    exact congrArg (fun p : M => e p - r x) (hinit ((phi true s).symm x))
  have hUeq : ∀ x t, t ∈ Icc s tau → U false x t = U true x t :=
    periodic_vector_eq_of_parabolic_bound
      (w₁ := U false) (w₂ := U true) (wx₁ := P false) (wx₂ := P true)
      (wxx₁ := Q false) (wxx₂ := Q true)
      (wt₁ := fun x t => A false x t • Q false x t + B false x t)
      (wt₂ := fun x t => A true x t • Q true x t + B true x t)
      (A := A false) hP hstau hmu (add_nonneg (mul_nonneg hL hR) hL)
      (hUCont false) (hUCont true) (hUper false) (hUper true)
      (fun x t ht =>
        ((hUC2 false t (Ioo_subset_Icc_self ht)).differentiable (by norm_num) x).hasDerivAt)
      (fun x t ht =>
        ((hUC2 true t (Ioo_subset_Icc_self ht)).differentiable (by norm_num) x).hasDerivAt)
      (fun x t ht =>
        ((hUC2 false t (Ioo_subset_Icc_self ht)).differentiable_deriv_two x).hasDerivAt)
      (fun x t ht =>
        ((hUC2 true t (Ioo_subset_Icc_self ht)).differentiable_deriv_two x).hasDerivAt)
      (fun x t ht => htime false t ht x) (fun x t ht => htime true t ht x)
      (fun x t ht => (hbounds x t (Ioo_subset_Icc_self ht)).1)
      (fun x t ht => norm_parabolic_difference_le hL hR rfl rfl
        (hbounds x t (Ioo_subset_Icc_self ht)).2.2.1
        (hbounds x t (Ioo_subset_Icc_self ht)).2.2.2
        (hbounds x t (Ioo_subset_Icc_self ht)).2.1) hUinit
  let theta : ℝ → ℝ → ℝ := fun x t => psi true (phi false t x) t
  have hagree (t : ℝ) (ht : t ∈ Icc s tau) (x : ℝ) : c x t = d (theta x t) t := by
    have hh := hUeq (phi false t x) t ht
    dsimp only [U, psi] at hh
    rw [OrderIso.symm_apply_apply] at hh
    exact heinj (sub_left_inj.mp hh)
  have hinput : ContinuousOn (fun z : ℝ × ℝ => (z.1, e (c z.1 z.2))) D :=
    continuousOn_fst.prodMk (c2ShrinkingCurve_embedded_closed_data (hCshort false) he).2.2.1
  have hPhiCont : ContinuousOn (fun z : ℝ × ℝ => phi false z.2 z.1) D := by
    have hraw : ContinuousOn
        (fun z : ℝ × ℝ => selectedCurveFootpoint r radius eps (z.1, e (c z.1 z.2))) D := by
      intro z hz
      have hf : ContinuousAt (selectedCurveFootpoint r radius eps) (z.1, e (c z.1 z.2)) :=
        (selectedCurveFootpoint_contDiffAt hr hm hM0 hB0.le hradius heps
        hlower hupper hsecond hsmall hmargin (z.1, e (c z.1 z.2))
        (hclose false z.2 hz.2 z.1)).1.continuousAt
      exact hf.comp_continuousWithinAt (f := fun z : ℝ × ℝ => (z.1, e (c z.1 z.2)))
        (hinput z hz)
    exact hraw.congr (fun z hz => (hdata false z.2 hz.2).1 z.1)
  have hPhiC1 : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => phi false z.2 z.1)
      (univ ×ˢ Ioo s tau) := by
    have hembed : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => e (c z.1 z.2))
        (univ ×ˢ Ioo s tau) := by
      simpa only [interior_Icc] using
        (c2ShrinkingCurve_embedded_interior_equation (hCshort false) he).1
    have hin : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => (z.1, e (c z.1 z.2)))
        (univ ×ˢ Ioo s tau) := contDiffOn_fst.prodMk hembed
    have hraw : ContDiffOn ℝ 1
        (fun z : ℝ × ℝ => selectedCurveFootpoint r radius eps (z.1, e (c z.1 z.2)))
        (univ ×ˢ Ioo s tau) := by
      intro z hz
      have hfoot := (selectedCurveFootpoint_contDiffAt hr hm hM0 hB0.le hradius heps
        hlower hupper hsecond hsmall hmargin (z.1, e (c z.1 z.2))
        (hclose false z.2 (Ioo_subset_Icc_self hz.2) z.1)).1.of_le
          (by simp : (1 : ℕ∞ω) ≤ ∞)
      exact (hfoot.comp z (hin.contDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz))).contDiffWithinAt
    exact hraw.congr (fun z hz => (hdata false z.2 (Ioo_subset_Icc_self hz.2)).1 z.1)
  have hThetaCont : ContinuousOn (Function.uncurry theta) D :=
    (hPsiCont true).comp (hPhiCont.prodMk continuousOn_snd)
      (fun _ hz => ⟨mem_univ _, hz.2⟩)
  have hThetaC1 : ContDiffOn ℝ 1 (Function.uncurry theta) (univ ×ˢ Ioo s tau) :=
    (hPsiC1 true).comp (hPhiC1.prodMk contDiffOn_snd)
      (fun _ hz => ⟨mem_univ _, hz.2⟩)
  have hThetaC2 (t : ℝ) (ht : t ∈ Icc s tau) : ContDiff ℝ 2 (fun x => theta x t) :=
    (hPsiC2 true t ht).comp (hPhiC2 false t ht)
  have hThetaPos (t : ℝ) (ht : t ∈ Ioo s tau) (x : ℝ) :
      0 < deriv (fun y => theta y t) x := by
    have ht' := Ioo_subset_Icc_self ht
    have hder := (((hPsiC2 true t ht').differentiable (by norm_num)
      (phi false t x)).hasDerivAt).comp x
      (((hPhiC2 false t ht').differentiable (by norm_num) x).hasDerivAt)
    change HasDerivAt (fun y => theta y t)
      (deriv (fun y => psi true y t) (phi false t x) * deriv (phi false t) x) x at hder
    rw [hder.deriv]
    exact mul_pos (hPsiPos true t ht' (phi false t x)) (hPhiPos false t ht' x)
  have hThetaInit (x : ℝ) : theta x s = x := by
    change (phi true s).symm (phi false s x) = x
    rw [hphis, OrderIso.symm_apply_apply]
  have hcomp : M63C2ShrinkingCurveOn F (fun x t => d (theta x t) t) (Icc s tau) :=
    c2_congr (hCshort false) (fun t ht x => (hagree t ht x).symm)
  have htheta := normal_relabeling_eq_initial_labels (hCshort true) hcomp
    (fun x => hThetaCont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_univ _, ht⟩))
    (fun x t ht => ((hThetaC1.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)).differentiableAt
        (by norm_num)).comp t ((differentiableAt_const x).prodMk differentiableAt_id))
    (fun t ht => (hThetaC2 t (Ioo_subset_Icc_self ht)).differentiable (by norm_num))
    hThetaPos hThetaInit
  exact ⟨tau, hstau, htauT, fun t ht x => by simpa only [htheta t ht x] using hagree t ht x⟩





theorem c2ShrinkingCurve_unique_closed_of_retraction
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {N : Set W} (hN : IsOpen N) (heN : range e ⊆ N) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ N) (hret : ∀ p, ρ (e p) = p)
    {s T : ℝ} {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    (hd : M63C2ShrinkingCurveOn F d (Icc s T))
    (hinit : ∀ x, c x s = d x s) :
    ∀ t ∈ Icc s T, ∀ x, c x t = d x t := by
  have heinj : Function.Injective e := (show Function.LeftInverse ρ e from hret).injective
  have hcE := (c2ShrinkingCurve_embedded_closed_data hc he).2.2.1
  have hdE := (c2ShrinkingCurve_embedded_closed_data hd he).2.2.1
  have heq := eqOn_Icc_of_forward_agreement
    (fun x => hcE.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_univ _, ht⟩))
    (fun x => hdE.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_univ _, ht⟩))
    (fun x => congrArg e (hinit x)) (fun u hu hsame => by
      have hsub : Icc u T ⊆ Icc s T := fun _ ht => ⟨hu.1.trans ht.1, ht.2⟩
      obtain ⟨tau, hutau, _htauT, hagree⟩ := exists_forward_c2ShrinkingCurve_agreement
        he hN heN hρ hret hu.2 (c2_restrict hc hsub) (c2_restrict hd hsub)
        (fun x => heinj (hsame x))
      exact ⟨tau, hutau, fun t ht _ x => congrArg e (hagree t ht x)⟩)
  exact fun t ht x => heinj (heq t ht x)

end PoincareConjecture.M63
