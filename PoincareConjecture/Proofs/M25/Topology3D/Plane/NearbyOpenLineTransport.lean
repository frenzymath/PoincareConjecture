import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineTube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedRadialSlide
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nearby_fixedTail_openLine_transport
    (C : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ))
    {a b s0 R : ℝ} (hab : a ≤ b) (hR : 0 < R)
    (hC : ContDiff ℝ ∞ C)
    (hinj : ∀ t ∈ Icc a b, Injective (fun u : ℝ => C ((t, s0), u)))
    (hreg : ∀ t ∈ Icc a b, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => C ((t, s0), v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → C (z, u) = (u, 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : (ℝ × ℝ) → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (F p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      (∀ z, (∀ u, C (z, u) = C ((z.1, s0), u)) →
        ∀ x, F z x = x ∧ (F z).symm x = x) ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc (s0 - r) (s0 + r),
        range (fun u : ℝ => F (t, s) (C ((t, s0), u))) =
          range (fun u : ℝ => C ((t, s), u)) := by
  let C0 : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p => C ((p.1.1, s0), p.2)
  have hC0 : ContDiff ℝ ∞ C0 :=
    hC.comp ((contDiff_fst.fst.prodMk contDiff_const).prodMk contDiff_snd)
  obtain ⟨m, hm, _, w, hw, _, T, hs, he, hT, hInv, hTtail⟩ :=
    exists_fixedTail_openLine_normalTube C0 (a := a) (b := b) (c := s0) (d := s0)
      hab le_rfl hR hC0 (fun z hz => hinj z.1 hz.1)
      (fun z hz u => hreg z.1 hz.1 u) (fun z u hu => htail (z.1, s0) u hu)
  let U : Set (ℝ × ℝ) := Ioo (a - m) (b + m) ×ˢ Ioo (s0 - m) (s0 + m)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hparameter (p : (ℝ × ℝ) × (ℝ × ℝ)) : (T p).1 = p.1 := by
    rw [he]
  have hzero (z : ℝ × ℝ) (u : ℝ) :
      T (z, (u, 0)) = (z, C ((z.1, s0), u)) := by
    simpa only [C0, zero_smul, add_zero] using he (z, (u, 0))
  have hsource0 (z : ℝ × ℝ) (hz : z ∈ U) (u : ℝ) : (z, (u, 0)) ∈ T.source := by
    rw [hs]
    refine ⟨hz, ?_⟩
    change |(0 : ℝ)| < w
    simpa only [abs_zero] using hw
  have hbaseU (t : ℝ) (ht : t ∈ Icc a b) : (t, s0) ∈ U := by
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith, by linarith⟩⟩
  let H : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × (ℝ × ℝ) := fun p => (p.1, C p)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk hC
  let V : Set ((ℝ × ℝ) × ℝ) := H ⁻¹' T.target
  have hV : IsOpen V := T.open_target.preimage hH.continuous
  let xi : (ℝ × ℝ) × ℝ → ℝ := fun p => (T.symm (H p)).2.1
  let eta : (ℝ × ℝ) × ℝ → ℝ := fun p => (T.symm (H p)).2.2
  have hcoords : ContDiffOn ℝ ∞ (fun p => T.symm (H p)) V :=
    hInv.comp hH.contDiffOn (fun _ hp => hp)
  have hxi : ContDiffOn ℝ ∞ xi V := hcoords.snd.fst
  have heta : ContDiffOn ℝ ∞ eta V := hcoords.snd.snd
  have hcoordinates (z : ℝ × ℝ) (hz : z ∈ U) (u : ℝ)
      (hc : C (z, u) = C ((z.1, s0), u)) :
      (z, u) ∈ V ∧ xi (z, u) = u ∧ eta (z, u) = 0 := by
    have hforward : T (z, (u, 0)) = H (z, u) := by
      rw [hzero]
      exact Prod.ext rfl hc.symm
    have hi : T.symm (H (z, u)) = (z, (u, 0)) := by
      rw [← hforward]
      exact T.left_inv (hsource0 z hz u)
    refine ⟨?_, congrArg (fun p => p.2.1) hi, congrArg (fun p => p.2.2) hi⟩
    change H (z, u) ∈ T.target
    rw [← hforward]
    exact T.map_source (hsource0 z hz u)
  have hbase (t : ℝ) (ht : t ∈ Icc a b) (u : ℝ) :
      ((t, s0), u) ∈ V ∧ xi ((t, s0), u) = u ∧ eta ((t, s0), u) = 0 :=
    hcoordinates (t, s0) (hbaseU t ht) u rfl
  have hctail (z : ℝ × ℝ) (hz : z ∈ U) (u : ℝ) (hu : R + 1 ≤ |u|) :
      (z, u) ∈ V ∧ xi (z, u) = u ∧ eta (z, u) = 0 := by
    have hforward : T (z, (u, 0)) = H (z, u) := by
      rw [hTtail z hz u 0 (by simpa only [abs_zero] using hw) hu]
      change (z, (u, 0)) = (z, C (z, u))
      rw [htail z u (by linarith)]
    have hi : T.symm (H (z, u)) = (z, (u, 0)) := by
      rw [← hforward]
      exact T.left_inv (hsource0 z hz u)
    refine ⟨?_, congrArg (fun p => p.2.1) hi, congrArg (fun p => p.2.2) hi⟩
    change H (z, u) ∈ T.target
    rw [← hforward]
    exact T.map_source (hsource0 z hz u)
  let D : (ℝ × ℝ) × ℝ → ℝ := fun p => fderiv ℝ xi p (0, 1)
  have hDcont : ContinuousOn D V :=
    (hxi.continuousOn_fderiv_of_isOpen hV (by simp)).clm_apply continuousOn_const
  have hder (z : ℝ × ℝ) (u : ℝ) (hp : (z, u) ∈ V) :
      HasDerivAt (fun v => xi (z, v)) (D (z, u)) u :=
    hasDerivAt_fiber ((hxi.contDiffAt (hV.mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt
  let A := w / 2
  have hA : 0 < A := half_pos hw
  have hAw : A < w := by dsimp [A]; linarith
  let L := R + 2
  have hL : 0 < L := by dsimp [L]; linarith
  let Good : Set ((ℝ × ℝ) × ℝ) :=
    V ∩ (fun p => (D p, eta p)) ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioo (-A) A)
  have hGood : IsOpen Good :=
    (hDcont.prodMk heta.continuousOn).isOpen_inter_preimage hV
      (isOpen_Ioi.prod isOpen_Ioo)
  have hK0 : (Icc a b ×ˢ ({s0} : Set ℝ)) ×ˢ Icc (-L) L ⊆ Good := by
    rintro ⟨⟨t, s⟩, u⟩ ⟨⟨ht, hs0⟩, _⟩
    have hss : s = s0 := hs0
    subst s
    have hline : (fun v => xi ((t, s0), v)) = id :=
      funext (fun v => (hbase t ht v).2.1)
    have hd := hder (t, s0) u (hbase t ht u).1
    rw [hline] at hd
    have hD : D ((t, s0), u) = 1 := hd.unique (hasDerivAt_id u)
    refine ⟨(hbase t ht u).1, ?_, ?_⟩
    · change 0 < D ((t, s0), u)
      rw [hD]
      exact zero_lt_one
    · change -A < eta ((t, s0), u) ∧ eta ((t, s0), u) < A
      rw [(hbase t ht u).2.2]
      exact ⟨neg_neg_of_pos hA, hA⟩
  obtain ⟨N0, W, hN0, _, hKN0, hLW, hNW⟩ :=
    generalized_tube_lemma (isCompact_Icc.prod isCompact_singleton)
      isCompact_Icc hGood hK0
  have hK0U : Icc a b ×ˢ ({s0} : Set ℝ) ⊆ U := by
    rintro ⟨t, s⟩ ⟨ht, hs0⟩
    have hss : s = s0 := hs0
    subst s
    exact hbaseU t ht
  obtain ⟨Nt, Ns, hNt, hNs, htNt, hsNs, hNtNs⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton (hN0.inter hU)
      (subset_inter hKN0 hK0U)
  obtain ⟨alpha, halpha, htalpha⟩ := exists_interval_margin hab hNt htNt
  obtain ⟨nu, hnu, hsnu⟩ := exists_interval_margin (a := s0) (b := s0) le_rfl hNs
    (by simpa only [Icc_self] using hsNs)
  let J : Set (ℝ × ℝ) :=
    Ioo (a - alpha) (b + alpha) ×ˢ Ioo (s0 - nu) (s0 + nu)
  have hJ : IsOpen J := isOpen_Ioo.prod isOpen_Ioo
  have hJN (z : ℝ × ℝ) (hz : z ∈ J) : z ∈ N0 ∩ U :=
    hNtNs ⟨htalpha hz.1, hsnu hz.2⟩
  have hnear (z : ℝ × ℝ) (hz : z ∈ J) (u : ℝ) :
      (z, u) ∈ V ∧ 0 < D (z, u) ∧ |eta (z, u)| < A := by
    by_cases hu : |u| ≤ L
    · have hg : (z, u) ∈ Good := hNW ⟨(hJN z hz).1, hLW (abs_le.mp hu)⟩
      exact ⟨hg.1, hg.2.1, abs_lt.mpr hg.2.2⟩
    · have hfar : R + 1 < |u| := by dsimp [L] at hu; linarith
      have hc := hctail z (hJN z hz).2 u hfar.le
      have heq : (fun v => xi (z, v)) =ᶠ[𝓝 u] id := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hfar] with v hv
        exact (hctail z (hJN z hz).2 v hv.le).2.1
      have hid := (hasDerivAt_id u).congr_of_eventuallyEq heq
      have hD : D (z, u) = 1 := (hder z u hc.1).unique hid
      refine ⟨hc.1, ?_, ?_⟩
      · rw [hD]
        exact zero_lt_one
      · rw [hc.2.2, abs_zero]
        exact hA
  let r := nu / 4
  have hr : 0 < r := div_pos hnu (by norm_num)
  obtain ⟨taut, htaut, htautBound, htautOne, htautZero⟩ :=
    exists_smooth_interval_cutoff a b (half_pos halpha)
  obtain ⟨taus, htaus, htausBound, htausOne, htausZero⟩ :=
    exists_smooth_interval_cutoff (s0 - r) (s0 + r) hr
  let tau : (ℝ × ℝ) → ℝ := fun z => taut z.1 * taus z.2
  have htau : ContDiff ℝ ∞ tau := (htaut.comp contDiff_fst).mul (htaus.comp contDiff_snd)
  have htauBound (z : ℝ × ℝ) : 0 ≤ tau z ∧ tau z ≤ 1 := by
    refine ⟨mul_nonneg (htautBound z.1).1 (htausBound z.2).1, ?_⟩
    dsimp only [tau]
    nlinarith [(htautBound z.1).1, (htautBound z.1).2,
      (htausBound z.2).1, (htausBound z.2).2]
  have htauOne (t s : ℝ) (ht : t ∈ Icc a b) (hsr : s ∈ Icc (s0 - r) (s0 + r)) :
      tau (t, s) = 1 := by
    simp only [tau, htautOne t ht, htausOne s hsr, one_mul]
  let K : Set (ℝ × ℝ) :=
    Icc (a - alpha / 2) (b + alpha / 2) ×ˢ Icc (s0 - 2 * r) (s0 + 2 * r)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKJ : K ⊆ J := by
    intro z hz
    dsimp [K] at hz
    dsimp [J, r] at *
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have houtside {l u x : ℝ} (hx : x ∉ Icc l u) : x ≤ l ∨ u ≤ x := by
    by_cases hl : l ≤ x
    · exact Or.inr (le_of_not_gt (fun h => hx ⟨hl, h.le⟩))
    · exact Or.inl (lt_of_not_ge hl).le
  have htauZero (z : ℝ × ℝ) (hz : z ∉ K) : tau z = 0 := by
    by_cases ht : z.1 ∈ Icc (a - alpha / 2) (b + alpha / 2)
    · have hzs : z.2 ∉ Icc (s0 - 2 * r) (s0 + 2 * r) := fun hs => hz ⟨ht, hs⟩
      have hzeroS : taus z.2 = 0 := by
        apply htausZero
        rcases houtside hzs with hl | hu
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      simp only [tau, hzeroS, mul_zero]
    · simp only [tau, htautZero z.1 (houtside ht), zero_mul]
  have hcutoff (f : (ℝ × ℝ) × ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ)) :
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => tau p.1 * f p) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.1 ∈ J
    · exact (htau.comp contDiff_fst).contDiffAt.mul
        (hf.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
    · have hpK : p.1 ∉ K := fun h => hp (hKJ h)
      have hn : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, q.1 ∉ K :=
        (hK.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpK
      have hconst : ContDiffAt ℝ ∞ (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) p :=
        contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hn] with q hq
      simp only [htauZero q.1 hq, zero_mul]
  have hJV : J ×ˢ (univ : Set ℝ) ⊆ V := fun p hp => (hnear p.1 hp.1 p.2).1
  let P : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 + tau p.1 * (xi p - p.2)
  have hP : ContDiff ℝ ∞ P :=
    contDiff_snd.add (hcutoff (fun p => xi p - p.2) ((hxi.mono hJV).sub contDiffOn_snd))
  have hPid (z : ℝ × ℝ) (hz : z ∉ J) (u : ℝ) : P (z, u) = u := by
    simp only [P, htauZero z (fun h => hz (hKJ h)), zero_mul, add_zero]
  have hPtail (z : ℝ × ℝ) (u : ℝ) (hu : L ≤ |u|) : P (z, u) = u := by
    by_cases hz : z ∈ J
    · have hc := hctail z (hJN z hz).2 u (by dsimp [L] at hu; linarith)
      simp only [P, hc.2.1, sub_self, mul_zero, add_zero]
    · exact hPid z hz u
  have hPpos (z : ℝ × ℝ) (u : ℝ) : 0 < deriv (fun v => P (z, v)) u := by
    by_cases hz : z ∈ J
    · have hdx := hder z u (hnear z hz u).1
      have hdP : HasDerivAt (fun v => P (z, v))
          (1 + tau z * (D (z, u) - 1)) u := by
        convert! (hasDerivAt_id u).add ((hdx.sub (hasDerivAt_id u)).const_mul (tau z))
      rw [hdP.deriv]
      convert lineInterpolation_derivative_pos (hnear z hz u).2.1 (htauBound z) using 1
      ring
    · have heq : (fun v => P (z, v)) = id := funext (hPid z hz)
      rw [heq, deriv_id]
      exact zero_lt_one
  have hPsurj (z : ℝ × ℝ) : Surjective (fun u => P (z, u)) := by
    apply surjective_of_eq_self_outside_interval
      (hP.continuous.comp (continuous_const.prodMk continuous_id)) (-L) L
    intro u hu
    apply hPtail
    rcases hu with hl | hr
    · exact (by linarith : L ≤ -u).trans (neg_le_abs u)
    · exact hr.trans (le_abs_self u)
  let Dfull := fiberDiffeomorph hP hPpos hPsurj
  have hDfull (p : (ℝ × ℝ) × ℝ) : Dfull p = (p.1, P p) :=
    fiberDiffeomorph_apply hP hPpos hPsurj p
  have hDinvparam (p : (ℝ × ℝ) × ℝ) : (Dfull.symm p).1 = p.1 := by
    have h := congrArg Prod.fst (Dfull.apply_symm_apply p)
    simpa only [hDfull] using h
  let G : (ℝ × ℝ) × ℝ → ℝ := fun p => (Dfull.symm p).2
  have hG : ContDiff ℝ ∞ G := Dfull.symm.contDiff.snd
  have hGleft (z : ℝ × ℝ) (u : ℝ) : P (z, G (z, u)) = u := by
    have h := congrArg Prod.snd (Dfull.apply_symm_apply (z, u))
    rw [hDfull] at h
    have hp : Dfull.symm (z, u) = (z, G (z, u)) := Prod.ext (hDinvparam _) rfl
    rw [hp] at h
    exact h
  have hGright (z : ℝ × ℝ) (u : ℝ) : G (z, P (z, u)) = u := by
    have h := congrArg Prod.snd (Dfull.symm_apply_apply (z, u))
    rw [hDfull] at h
    exact h
  have hGtail (z : ℝ × ℝ) (u : ℝ) (hu : L ≤ |u|) : G (z, u) = u := by
    simpa only [hPtail z u hu] using hGright z u
  let g : (ℝ × ℝ) × ℝ → ℝ := fun p => tau p.1 * eta (p.1, G p)
  have hg : ContDiff ℝ ∞ g := hcutoff (fun p => eta (p.1, G p))
    (heta.comp (contDiff_fst.prodMk hG).contDiffOn (fun p hp => (hnear p.1 hp.1 _).1))
  have hgBound (p : (ℝ × ℝ) × ℝ) : |g p| < A := by
    by_cases hz : p.1 ∈ J
    · simp only [g, abs_mul, abs_of_nonneg (htauBound p.1).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (htauBound p.1).2).trans_lt
        (hnear p.1 hz (G p)).2.2
    · simp only [g, htauZero p.1 (fun h => hz (hKJ h)), zero_mul, abs_zero]
      exact hA
  have hgZero (z : ℝ × ℝ) (u : ℝ) (hu : z ∉ K ∨ L ≤ |u|) : g (z, u) = 0 := by
    rcases hu with hz | hu
    · simp only [g, htauZero z hz, zero_mul]
    · by_cases hz : z ∈ J
      · have hc := hctail z (hJN z hz).2 u (by dsimp [L] at hu; linarith)
        simp only [g, hGtail z u hu, hc.2.2, mul_zero]
      · simp only [g, htauZero z (fun h => hz (hKJ h)), zero_mul]
  obtain ⟨F, hF, hFi, hQ, hSupport, hStationary, hGraph⟩ :=
    exists_relative_openTube_graph_transport T hK (fun z hz => (hJN z (hKJ hz)).2)
      hA hAw hL hs hparameter hT hInv g hg hgBound hgZero
  refine ⟨r, hr, F, hF, hFi, hQ, hSupport, ?_, ?_⟩
  · intro z hstat x
    apply hStationary z ?_ x
    intro u
    by_cases hz : z ∈ J
    · have hc := hcoordinates z (hJN z hz).2 (G (z, u)) (hstat _)
      simp only [g, hc.2.2, mul_zero]
    · exact hgZero z u (Or.inl (fun h => hz (hKJ h)))
  · intro t ht s hsr
    let z : ℝ × ℝ := (t, s)
    have hzK : z ∈ K := by
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ⟨by linarith [hsr.1], by linarith [hsr.2]⟩⟩
    have hzJ := hKJ hzK
    have hzU := (hJN z hzJ).2
    have htau1 : tau z = 1 := htauOne t s ht hsr
    have hPxi (v : ℝ) : P (z, v) = xi (z, v) := by
      dsimp only [P]
      rw [htau1]
      ring
    have haction (u : ℝ) : F z (C ((t, s0), u)) = C (z, G (z, u)) := by
      have hp : H (z, G (z, u)) ∈ T.target := (hnear z hzJ _).1
      have hparamInv : (T.symm (H (z, G (z, u)))).1 = z := by
        have h := congrArg Prod.fst (T.right_inv hp)
        simpa only [hparameter, H] using h
      have hxiG : xi (z, G (z, u)) = u := by
        rw [← hPxi]
        exact hGleft z u
      have hgin : g (z, u) = eta (z, G (z, u)) := by
        simp only [g, htau1, one_mul]
      have hinv : T.symm (H (z, G (z, u))) = (z, (u, g (z, u))) := by
        exact Prod.ext hparamInv (Prod.ext hxiG hgin.symm)
      have hout : (T (z, (u, g (z, u)))).2 = C (z, G (z, u)) := by
        rw [← hinv]
        exact congrArg Prod.snd (T.right_inv hp)
      have h := hGraph z hzU u
      rw [hzero] at h
      exact h.trans hout
    apply Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨G (z, u), (haction u).symm⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨P (z, u), ?_⟩
      change F z (C ((t, s0), P (z, u))) = C (z, u)
      rw [haction, hGright]

end PoincareConjecture.M25.Topology3D
