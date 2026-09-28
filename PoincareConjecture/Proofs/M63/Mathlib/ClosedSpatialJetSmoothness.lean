import PoincareConjecture.Proofs.M63.Mathlib.CompactPathDerivative
import PoincareConjecture.Proofs.M63.Mathlib.SpatialJetComposition
import PoincareConjecture.Proofs.M63.Mathlib.SpatialJetPrimitive
import PoincareConjecture.Proofs.M03.Existence.DeTurckEndpointCalculusNative
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open PoincareConjecture.DeTurckEndpointCalculusNative
open scoped ContDiff Topology

theorem contDiffOn_infty_Icc_of_spatial_jets_and_finite_sources
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 < T) {q R : ℝ → ℝ → E}
    (hspace : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (q t))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Icc 0 T ×ˢ univ))
    (hprimitive : ∀ t ∈ Icc 0 T, ∀ x,
      q t x = q 0 x + ∫ r in 0..t, R r x)
    (hsource : ∀ m : ℕ, ∃ Φ : (ℝ × (E × (E × E))) → E,
      ContDiff ℝ m Φ ∧ ∀ t ∈ Icc 0 T, ∀ x,
        R t x = Φ (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x)))) :
    ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
  let S : Set (ℝ × ℝ) := Icc 0 T ×ˢ univ
  let Q (k : ℕ) (t x : ℝ) := iteratedDeriv k (q t) x
  let P (t x : ℝ) := (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x)))
  have hQs (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (Q k t) := by
    induction k with
    | zero => simpa only [Q, iteratedDeriv_zero] using hspace t ht
    | succ k ih =>
      change ContDiff ℝ ∞ (iteratedDeriv (k + 1) (q t))
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2
  have hQd (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      HasDerivAt (Q k t) (Q (k + 1) t x) x := by
    dsimp only [Q]
    rw [iteratedDeriv_succ]
    exact ((hspace t ht).differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
  have hPs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (P t) := by
    have hfirst : ContDiff ℝ ∞ (deriv (q t)) := by
      simpa only [Q, iteratedDeriv_one] using hQs 1 t ht
    exact contDiff_const.prodMk ((hspace t ht).prodMk (hfirst.prodMk (hQs 2 t ht)))
  have hRs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (R t) := by
    apply contDiff_infty.mpr
    intro m
    obtain ⟨Φ, hΦ, heq⟩ := hsource m
    have hP : ContDiff ℝ m (P t) := (hPs t ht).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
    have he : R t = Φ ∘ P t := funext (heq t ht)
    rw [he]
    exact hΦ.comp hP
  have hPjet (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) : iteratedDeriv j (P t) =
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
  have hRreg (m : ℕ) (hQ : ∀ j : ℕ, ContDiffOn ℝ m
      (fun z : ℝ × ℝ => Q j z.1 z.2) S) (k : ℕ) :
      ContDiffOn ℝ m (fun z : ℝ × ℝ => iteratedDeriv k (R z.1) z.2) S := by
    obtain ⟨Φ, hΦ, heq⟩ := hsource (m + k)
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
    have hcomp := contDiffOn_iteratedDeriv_comp_of_spatial_jets
      (S := S) (f := fun z : ℝ × ℝ => P z.1) (x := Prod.snd)
      isOpen_univ (n := (m : ℕ∞)) (m := ((m + k : ℕ) : ℕ∞)) (k := k)
      (by simp) hΦ.contDiffOn
      (fun z hz => (hPs z.1 hz.1).contDiffAt) (fun _ _ => mem_univ _) hPjets
    apply hcomp.congr
    intro z hz
    have he : R z.1 = Φ ∘ P z.1 := funext (heq z.1 hz.1)
    rw [he]
  have hRc (k : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (R z.1) z.2) S :=
    (hRreg 0 (fun j => contDiffOn_zero.mpr (hjets j)) k).continuousOn
  have hprim := iteratedDeriv_primitive_and_hasDerivAt hT.le hspace hRs hRc hprimitive
  let Qp (k : ℕ) (x : ℝ) : C(Icc (0 : ℝ) T, E) :=
    ⟨fun t => Q k t x, (hjets k).comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun t => ⟨t.2, mem_univ _⟩)⟩
  have hQpc (k : ℕ) : Continuous (Qp k) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hjets k).comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
      (fun z => ⟨z.2.2, mem_univ _⟩)
  have hQpd (k : ℕ) (x : ℝ) : HasDerivAt (Qp k) (Qp (k + 1) x) x :=
    hasDerivAt_compact_curry isOpen_univ (Qp k) (Qp (k + 1)) (mem_univ x)
      (hQpc (k + 1)).continuousAt (fun y _ t => hQd k t t.2 y)
  have hQt (k : ℕ) (x t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => Qp k x (projIcc 0 T hT.le s))
        (iteratedDeriv k (R t) x) (Icc 0 T) t := by
    let Rp : C(Icc (0 : ℝ) T, E) :=
      ⟨fun r => iteratedDeriv k (R r) x, (hRc k).comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun r => ⟨r.2, mem_univ _⟩)⟩
    have hd := (integralOperator_hasDerivWithinAt hT.le Rp ht).const_add (Q k 0 x)
    apply hd.congr_of_mem _ ht
    intro s hs
    rw [projIcc_of_mem _ hs, IccExtend_of_mem hT.le _ hs, integralOperator_apply]
    change Q k s x = Q k 0 x + ∫ r in 0..s, IccExtend hT.le Rp r
    dsimp only [Q]
    rw [(hprim k).1 s hs x]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    rw [IccExtend_of_mem hT.le Rp ⟨hr.1, hr.2.trans hs.2⟩]
    rfl
  let D (k : ℕ) (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv k (R z.1) z.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (Q (k + 1) z.1 z.2))
  have hdiff (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ S) :
      HasFDerivWithinAt (fun w : ℝ × ℝ => Q k w.1 w.2) (D k z) S z := by
    have hd := hasFDerivWithinAt_path_eval (projIcc 0 T hT.le) continuous_projIcc
      (Qp k) (ContinuousLinearMap.toSpanSingleton ℝ (Qp (k + 1) z.2))
      (iteratedDeriv k (R z.1) z.2) (hQpd k z.2).hasFDerivAt (hQt k z.2 z.1 hz.1)
    have hmap : ((ContinuousLinearMap.toSpanSingleton ℝ
        (iteratedDeriv k (R z.1) z.2)).coprod
        ((ContinuousMap.evalCLM ℝ (projIcc 0 T hT.le z.1)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (Qp (k + 1) z.2)))) = D k z := by
      apply ContinuousLinearMap.ext
      intro v
      change v.1 • iteratedDeriv k (R z.1) z.2 +
        v.2 • Q (k + 1) (projIcc 0 T hT.le z.1) z.2 =
          v.1 • iteratedDeriv k (R z.1) z.2 + v.2 • Q (k + 1) z.1 z.2
      rw [projIcc_of_mem _ hz.1]
    rw [hmap] at hd
    have heq : EqOn (fun w : ℝ × ℝ => Q k w.1 w.2)
        (fun w : ℝ × ℝ => Qp k w.2 (projIcc 0 T hT.le w.1)) S := by
      intro w hw
      change Q k w.1 w.2 = Q k (projIcc 0 T hT.le w.1) w.2
      rw [projIcc_of_mem _ hw.1]
    exact hd.congr' heq hz
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
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
      have hs := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS).mpr
        ⟨by simp, D k, hD, hdiff k⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hs
  apply contDiffOn_infty.mpr
  intro m
  simpa only [Q, iteratedDeriv_zero, Function.uncurry_def, S] using hall m 0
