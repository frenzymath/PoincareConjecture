import PoincareConjecture.Proofs.M63.Mathlib.SpatialJetComposition
import PoincareConjecture.Proofs.M63.Mathlib.SpatialJetPrimitive
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousPartialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology





theorem contDiffOn_infty_of_spatial_jets_and_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {q : ℝ → ℝ → E} {U : Set (ℝ × (E × (E × E)))}
    (hU : IsOpen U) {Φ : (ℝ × (E × (E × E))) → E}
    (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hspace : ∀ t ∈ Ioo a b, ContDiff ℝ ∞ (q t))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Ioo a b ×ˢ univ))
    (hguard : ∀ t ∈ Ioo a b, ∀ x,
      (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x))) ∈ U)
    (htime : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r => q r x)
      (Φ (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x)))) t) :
    ContDiffOn ℝ ∞ (Function.uncurry q) (Ioo a b ×ˢ univ) := by
  let S : Set (ℝ × ℝ) := Ioo a b ×ˢ univ
  let Q (k : ℕ) (t x : ℝ) := iteratedDeriv k (q t) x
  let P (t x : ℝ) := (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x)))
  let R (t x : ℝ) := Φ (P t x)
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_univ
  have hQs (k : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ ∞ (Q k t) := by
    induction k with
    | zero => simpa only [Q, iteratedDeriv_zero] using hspace t ht
    | succ k ih =>
      change ContDiff ℝ ∞ (iteratedDeriv (k + 1) (q t))
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2
  have hQd (k : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (Q k t) (Q (k + 1) t x) x := by
    dsimp only [Q]
    rw [iteratedDeriv_succ]
    exact ((hspace t ht).differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
  have hPs (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ ∞ (P t) := by
    have hfirst : ContDiff ℝ ∞ (deriv (q t)) := by
      simpa only [Q, iteratedDeriv_one] using hQs 1 t ht
    exact contDiff_const.prodMk ((hspace t ht).prodMk (hfirst.prodMk (hQs 2 t ht)))
  have hRs (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ ∞ (R t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hΦ.contDiffAt (hU.mem_nhds (hguard t ht x))).comp x (hPs t ht).contDiffAt
  have hPjet (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : iteratedDeriv j (P t) =
      fun x => (iteratedDeriv j (fun _ : ℝ => t) x,
        (Q j t x, (Q (j + 1) t x, Q (j + 2) t x))) := by
    induction j with
    | zero =>
      funext x
      simp only [iteratedDeriv_zero, P, Q, zero_add, iteratedDeriv_one]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hc : ContDiff ℝ ∞ (fun _ : ℝ => t) := contDiff_const
      have hd := (hc.differentiable_iteratedDeriv j
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j) x).hasDerivAt
      have hp := hd.prodMk ((hQd j t ht x).prodMk
        ((hQd (j + 1) t ht x).prodMk (hQd (j + 2) t ht x)))
      simpa only [iteratedDeriv_succ, Nat.add_assoc] using hp.deriv
  have hRreg (m : ℕ∞) (hQ : ∀ j : ℕ, ContDiffOn ℝ m
      (fun z : ℝ × ℝ => Q j z.1 z.2) S) (k : ℕ) :
      ContDiffOn ℝ m (fun z : ℝ × ℝ => iteratedDeriv k (R z.1) z.2) S := by
    have hPjets (j : ℕ) : ContDiffOn ℝ m
        (fun z : ℝ × ℝ => iteratedDeriv j (P z.1) z.2) S := by
      have hconst : ContDiffOn ℝ m
          (fun z : ℝ × ℝ => iteratedDeriv j (fun _ : ℝ => z.1) z.2) S := by
        by_cases hj : j = 0
        · simpa only [iteratedDeriv_const, hj, if_true] using
            (contDiffOn_fst : ContDiffOn ℝ m (Prod.fst : ℝ × ℝ → ℝ) S)
        · simpa only [iteratedDeriv_const, hj, if_false] using
            (contDiffOn_const : ContDiffOn ℝ m (fun _ : ℝ × ℝ => (0 : ℝ)) S)
      apply (hconst.prodMk ((hQ j).prodMk ((hQ (j + 1)).prodMk (hQ (j + 2))))).congr
      intro z hz
      exact congrFun (hPjet j z.1 hz.1) z.2
    exact contDiffOn_iteratedDeriv_comp_of_spatial_jets hU (m := ⊤) (by simp) hΦ
      (fun z hz => (hPs z.1 hz.1).contDiffAt) (fun z hz => hguard z.1 hz.1 z.2) hPjets
  have hRc (k : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (R z.1) z.2) S :=
    (hRreg 0 (fun j => contDiffOn_zero.mpr (hjets j)) k).continuousOn
  have hqc : ContinuousOn (Function.uncurry q) S := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def, S] using hjets 0
  have hRzero : ContinuousOn (Function.uncurry R) S := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hRc 0
  have hQt (k : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun r => Q k r x) (iteratedDeriv k (R t) x) t := by
    let c := (a + t) / 2
    let d := (t + b) / 2
    have hct : c < t := by dsimp only [c]; linarith [ht.1]
    have htd : t < d := by dsimp only [d]; linarith [ht.2]
    have hcd : c ≤ d := hct.le.trans htd.le
    have hsub : Icc c d ⊆ Ioo a b := by
      intro r hr
      dsimp only [c, d] at hr
      constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
    have hp : ∀ s ∈ Icc c d, ∀ y,
        q s y = q c y + ∫ r in c..s, R r y := by
      intro s hs y
      have hm : MapsTo (fun r : ℝ => (r, y)) (Icc c s) S :=
        fun r hr => ⟨hsub ⟨hr.1, hr.2.trans hs.2⟩, mem_univ _⟩
      have hcontq : ContinuousOn (fun r => q r y) (Icc c s) :=
        hqc.comp (continuous_id.prodMk continuous_const).continuousOn hm
      have hcontR : ContinuousOn (fun r => R r y) (Icc c s) :=
        hRzero.comp (continuous_id.prodMk continuous_const).continuousOn hm
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hcontq
        (fun r hr => htime r (hsub ⟨hr.1.le, hr.2.le.trans hs.2⟩) y)
        (ContinuousOn.intervalIntegrable_of_Icc hs.1 hcontR)
      rw [hi]
      abel
    have hprimitive := iteratedDeriv_primitive_and_hasDerivAt hcd
      (fun r hr => hspace r (hsub hr)) (fun r hr => hRs r (hsub hr))
      (fun j => (hRc j).mono (prod_mono hsub Subset.rfl)) hp
    exact (hprimitive k).2 t ⟨hct, htd⟩ x
  let D (k : ℕ) (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv k (R z.1) z.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (Q (k + 1) z.1 z.2))
  have hdiff (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ S) :
      HasFDerivAt (fun w : ℝ × ℝ => Q k w.1 w.2) (D k z) z := by
    have hmem : ∀ᶠ w in 𝓝 z, w ∈ S := hS.mem_nhds hz
    have he₁ : ∀ᶠ w in 𝓝 z, HasFDerivAt (fun t => Q k t w.2)
        (ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv k (R w.1) w.2)) w.1 :=
      hmem.mono fun w hw => (hQt k w.1 hw.1 w.2).hasFDerivAt
    have he₂ : ∀ᶠ w in 𝓝 z, HasFDerivAt (Q k w.1)
        (ContinuousLinearMap.toSpanSingleton ℝ (Q (k + 1) w.1 w.2)) w.2 :=
      hmem.mono fun w hw => (hQd k w.1 hw.1 w.2).hasFDerivAt
    have hc₁ := (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn
      (hRc k)
    have hc₂ := (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn
      (hjets (k + 1))
    exact (hasStrictFDerivAt_uncurry_coprod (f := Q k)
      (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv k (R t) x))
      (f₂ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (Q (k + 1) t x)) he₁ he₂
      (hc₁.continuousAt (hS.mem_nhds hz)) (hc₂.continuousAt (hS.mem_nhds hz))).hasFDerivAt
  have hall : ∀ m : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ m (fun z : ℝ × ℝ => Q k z.1 z.2) S := by
    intro m
    induction m with
    | zero => exact fun k => contDiffOn_zero.mpr (hjets k)
    | succ m ih =>
      intro k
      have hD : ContDiffOn ℝ m (D k) S := by
        apply contDiffOn_clm_apply.mpr
        intro v
        change ContDiffOn ℝ m (fun z : ℝ × ℝ =>
          v.1 • iteratedDeriv k (R z.1) z.2 + v.2 • Q (k + 1) z.1 z.2) S
        exact ((hRreg m ih k).const_smul v.1).add ((ih (k + 1)).const_smul v.2)
      have hs := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn).mpr
        ⟨by simp, D k, hD, fun z hz => (hdiff k z hz).hasFDerivWithinAt⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hs
  apply contDiffOn_infty.mpr
  intro m
  simpa only [Q, iteratedDeriv_zero, Function.uncurry_def, S] using hall m 0
