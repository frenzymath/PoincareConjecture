
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Variational









set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set
open scoped ContDiff NNReal

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {P G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

noncomputable local instance : NormedAddCommGroup (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace


private def variationCoeff (A D : G →L[ℝ] G) : (G × G) →L[ℝ] (G × G) :=
  (A.comp (ContinuousLinearMap.fst ℝ G G)).prod
    (D.comp (ContinuousLinearMap.fst ℝ G G) + A.comp (ContinuousLinearMap.snd ℝ G G))

private theorem variationCoeff_apply (A D : G →L[ℝ] G) (z : G × G) :
    variationCoeff A D z = (A z.1, D z.1 + A z.2) := rfl

private theorem variationCoeff_contDiffOn
    {A D : P × ℝ → G →L[ℝ] G} {S : Set (P × ℝ)}
    (hA : ContDiffOn ℝ ∞ A S) (hD : ContDiffOn ℝ ∞ D S) :
    ContDiffOn ℝ ∞ (fun q => variationCoeff (A q) (D q)) S := by
  letI : NormedAddCommGroup ((G × G) →L[ℝ] G) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ ((G × G) →L[ℝ] G) := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup ((G × G) →L[ℝ] (G × G)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ ((G × G) →L[ℝ] (G × G)) := ContinuousLinearMap.toNormedSpace
  exact (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × G) (F := G) (G := G) ℝ).contDiff.comp_contDiffOn
    ((hA.clm_comp contDiffOn_const).prodMk
      ((hD.clm_comp contDiffOn_const).add (hA.clm_comp contDiffOn_const)))



theorem linearODE_contDiffOn_nat
    (n : ℕ) (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry Φ) (U ×ˢ Icc a b) := by
  induction n generalizing G with
  | zero =>
      exact contDiffOn_zero.mpr (linearODE_continuousOn A hab hU hA Φ hinit hsol)
  | succ n ih =>
      rcases eq_or_lt_of_le hab with heq | hlt
      · have h0 : ContDiffOn ℝ (n + 1 : WithTop ℕ∞)
            (fun q : P × ℝ => Φ q.1 a) (U ×ˢ Icc a b) :=
          (hinit.of_le (by exact_mod_cast (show (n + 1 : ℕ∞) ≤ ⊤ from le_top))).comp
            contDiffOn_fst (fun _ hq => hq.1)
        apply h0.congr
        intro q hq
        have ht : q.2 = a := by obtain ⟨ht₁, ht₂⟩ := hq.2; linarith
        simp only [Function.uncurry, ht]
      have hΦn : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry Φ) (U ×ˢ Icc a b) :=
        ih A hA Φ hinit hsol
      have hD : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun q : P × ℝ => fderiv ℝ (fun p => Φ p q.2) q.1) (U ×ˢ Icc a b) := by
        rw [contDiffOn_clm_apply]
        intro v
        let DA : P → ℝ → G →L[ℝ] G := fun p t => (fderiv ℝ (fun x => A x t) p) v
        let B : P → ℝ → (G × G) →L[ℝ] (G × G) :=
          fun p t => variationCoeff (A p t) (DA p t)
        let Z : P → ℝ → G × G := fun p t => (Φ p t, (fderiv ℝ (fun x => Φ x t) p) v)
        have hDA : ContDiffOn ℝ ∞ (Function.uncurry DA) (U ×ˢ Icc a b) :=
          (contDiffOn_fderiv_param_Icc hlt hU hA).clm_apply contDiffOn_const
        have hB : ContDiffOn ℝ ∞ (Function.uncurry B) (U ×ˢ Icc a b) :=
          variationCoeff_contDiffOn hA hDA
        have hZinit : ContDiffOn ℝ ∞ (fun p => Z p a) U :=
          hinit.prodMk ((hinit.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)
        have hZsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
            HasDerivWithinAt (Z p) (B p t (Z p t)) (Icc a b) t := by
          intro p hp t ht
          have hv := (linearODE_hasDerivWithinAt_fderiv_param A hab hU hA Φ hinit hsol hp ht).clm_apply
            (hasDerivWithinAt_const (x := t) (s := Icc a b) (c := v))
          have hpair := (hsol p hp t ht).prodMk hv
          simpa [Z, B, DA, variationCoeff_apply] using hpair
        exact (ih B hB Z hZinit hZsol).snd
      have htime : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun q : P × ℝ => A q.1 q.2 (Φ q.1 q.2)) (U ×ˢ Icc a b) :=
        (hA.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).clm_apply hΦn
      let D : P × ℝ → (P × ℝ) →L[ℝ] G := fun q =>
        (fderiv ℝ (fun p => Φ p q.2) q.1).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (A q.1 q.2 (Φ q.1 q.2)))
      have htimeL : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun q : P × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (A q.1 q.2 (Φ q.1 q.2)))
          (U ×ˢ Icc a b) :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).contDiff.comp_contDiffOn htime
      have hDn : ContDiffOn ℝ (n : WithTop ℕ∞) D (U ×ˢ Icc a b) := by
        exact (ContinuousLinearMap.coprodEquivL ℝ (E := P) (F := ℝ) (G := G)).contDiff.comp_contDiffOn
          (hD.prodMk htimeL)
      have hder : ∀ q ∈ U ×ˢ Icc a b,
          HasFDerivWithinAt (Function.uncurry Φ) (D q) (U ×ˢ Icc a b) q := by
        intro q hq
        have hs := linearODE_contDiffOn_spatial A hab hU hA Φ hinit hsol hq.2
        have hx := (((hs q.1 hq.1).contDiffAt (hU.mem_nhds hq.1)).differentiableAt
          (by simp)).hasFDerivAt
        apply Poincare.hasFDerivWithinAt_prod_of_continuous_partial (convex_Icc a b) hq hx
          (fun r hr => (hsol r.1 hr.1 r.2 hr.2).hasFDerivWithinAt)
        exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp_continuousWithinAt
          ((hA.continuousOn.clm_apply
            (linearODE_continuousOn A hab hU hA Φ hinit hsol)) q hq)
      have hud : UniqueDiffOn ℝ (U ×ˢ Icc a b) := hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hlt)
      change ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (Function.uncurry Φ) (U ×ˢ Icc a b)
      exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hud).mpr
        ⟨by simp, D, hDn, hder⟩



theorem linearODE_contDiffOn
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ ∞ (Function.uncurry Φ) (U ×ˢ Icc a b) := by
  rw [contDiffOn_infty]
  intro n
  exact linearODE_contDiffOn_nat n A hab hU hA Φ hinit hsol



theorem transportCurveOn_contDiffOn_closed
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (A : P → ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (hcont : ∀ p, ContinuousOn (A p) (Icc a b)) {K : P → ℝ≥0}
    (hK : ∀ p, ∀ t ∈ Icc a b, ‖A p t‖₊ ≤ K p) :
    ContDiffOn ℝ ∞
      (fun q : P × ℝ => transportCurveOn (A q.1) hab (hcont q.1) (hK q.1) q.2)
      (U ×ˢ Icc a b) := by
  let : NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup ((V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
  apply linearODE_contDiffOn
    (fun p s => ContinuousLinearMap.compL ℝ V V V (A p s)) hab hU
    ((ContinuousLinearMap.compL ℝ V V V).contDiff.comp_contDiffOn hA)
    (fun p s => transportCurveOn (A p) hab (hcont p) (hK p) s) ?_ ?_
  · apply (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : P => ContinuousLinearMap.id ℝ V) U).congr
    intro p hp
    rw [transportCurveOn_left]
  · intro p hp s hs
    exact transportCurveOn_hasDerivWithinAt (A p) hab (hcont p) (hK p) hs

end PoincareConjecture.RicciFlow.Frame

end
