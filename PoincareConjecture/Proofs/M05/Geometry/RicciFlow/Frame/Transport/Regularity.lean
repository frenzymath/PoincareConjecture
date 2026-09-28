
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport
import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import PoincareConjecture.Proofs.M05.Analysis.Calculus.WithinProduct














set_option autoImplicit false
set_option maxHeartbeats 800000

open Set
open scoped ContDiff NNReal

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

noncomputable local instance transportEndoNormedAddCommGroup :
    NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance transportEndoNormedSpace :
    NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

noncomputable local instance transportEndoEndoNormedAddCommGroup :
    NormedAddCommGroup ((V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance transportEndoEndoNormedSpace :
    NormedSpace ℝ ((V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace



theorem transportCurveOn_contDiffOn
    (A : P → ℝ → V →L[ℝ] V) {a b c d : ℝ} (hab : a ≤ b)
    (hca : c < a) (hbd : b < d) {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Ioo c d))
    (hcont : ∀ p, ContinuousOn (A p) (Icc a b)) {K : P → ℝ≥0}
    (hK : ∀ p, ∀ t ∈ Icc a b, ‖A p t‖₊ ≤ K p) :
    ContDiffOn ℝ ∞
      (fun q : P × ℝ => transportCurveOn (A q.1) hab (hcont q.1) (hK q.1) q.2)
      (U ×ˢ Icc a b) := by
  let B : P → ℝ → (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
    fun p t => ContinuousLinearMap.compL ℝ V V V (A p t)
  let Ψ := Poincare.ODE.LocalFlow.linearODESolution B c d a
    (fun _ : P => ContinuousLinearMap.id ℝ V)
  have ha : a ∈ Ioo c d := ⟨hca, hab.trans_lt hbd⟩
  have hsub : Icc a b ⊆ Ioo c d := fun t ht =>
    ⟨hca.trans_le ht.1, ht.2.trans_lt hbd⟩
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) (U ×ˢ Ioo c d) :=
    (ContinuousLinearMap.compL ℝ V V V).contDiff.comp_contDiffOn hA
  have hΨ : ContDiffOn ℝ ∞ (Function.uncurry Ψ) (U ×ˢ Ioo c d) :=
    Poincare.ODE.LocalFlow.linearODESolution_contDiffOn_top ha hU hB contDiffOn_const
  have heq : ∀ p ∈ U,
      EqOn (transportCurveOn (A p) hab (hcont p) (hK p)) (Ψ p) (Icc a b) := by
    intro p hp
    apply transportCurveOn_eqOn (A p) hab (hcont p) (hK p)
    · exact Poincare.ODE.LocalFlow.linearODESolution_init _ _ _ _ _ _
    · intro t ht
      exact (Poincare.ODE.LocalFlow.linearODESolution_hasDerivAt
        ha hB.continuousOn hp (hsub ht)).hasDerivWithinAt
  exact (hΨ.mono (prod_mono Subset.rfl hsub)).congr
    (fun q hq => heq q.1 hq.1 hq.2)

private def cosineClock (a b s : ℝ) : ℝ := a + (b - a) * (1 - Real.cos s) / 2

private theorem cosineClock_mem {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    cosineClock a b s ∈ Icc a b := by
  have hc₁ := Real.neg_one_le_cos s
  have hc₂ := Real.cos_le_one s
  dsimp [cosineClock]
  constructor <;> nlinarith

private theorem cosineClock_hasDerivAt (a b s : ℝ) :
    HasDerivAt (cosineClock a b) ((b - a) * Real.sin s / 2) s := by
  have hd : HasDerivAt (fun r => a + (b - a) * (1 - Real.cos r) / 2)
      ((b - a) * (0 - -Real.sin s) / 2) s :=
    (((((hasDerivAt_const s (1 : ℝ)).sub (Real.hasDerivAt_cos s)).const_mul
      (b - a)).div_const 2).const_add a)
  convert hd using 1 <;> first | rfl | ring

private theorem cosineClock_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cosineClock a b) := by
  exact contDiff_const.add
    ((contDiff_const.mul (contDiff_const.sub Real.contDiff_cos)).div_const 2)

private def cosineClockInv (a b t : ℝ) : ℝ :=
  Real.arccos (1 - 2 * (t - a) / (b - a))

private theorem cosineClockInv_continuous (a b : ℝ) : Continuous (cosineClockInv a b) := by
  exact Real.continuous_arccos.comp
    (continuous_const.sub ((continuous_const.mul (continuous_id.sub continuous_const)).div_const _))

private theorem cosineClockInv_mem (a b t : ℝ) :
    cosineClockInv a b t ∈ Ioo (-1) (Real.pi + 1) := by
  constructor <;> dsimp [cosineClockInv] <;>
    linarith [Real.arccos_nonneg (1 - 2 * (t - a) / (b - a)),
      Real.arccos_le_pi (1 - 2 * (t - a) / (b - a))]

private theorem cosineClock_inv {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    cosineClock a b (cosineClockInv a b t) = t := by
  have hr₁ : -1 ≤ 1 - 2 * (t - a) / (b - a) := by
    have hdiv : 2 * (t - a) / (b - a) ≤ 2 :=
      (div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith [ht.2])
    linarith
  have hr₂ : 1 - 2 * (t - a) / (b - a) ≤ 1 := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sub_nonneg.mpr ht.1)) (sub_nonneg.mpr hab.le)
    linarith
  dsimp [cosineClock, cosineClockInv]
  rw [Real.cos_arccos hr₁ hr₂]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

private theorem cosineClockInv_contDiffOn (a b : ℝ) :
    ContDiffOn ℝ ∞ (cosineClockInv a b) (Ioo a b) := by
  intro t ht
  have hab : 0 < b - a := sub_pos.mpr (ht.1.trans ht.2)
  have h₁ : -1 < 1 - 2 * (t - a) / (b - a) := by
    have hdiv : 2 * (t - a) / (b - a) < 2 :=
      (div_lt_iff₀ hab).mpr (by linarith [ht.2])
    linarith
  have h₂ : 1 - 2 * (t - a) / (b - a) < 1 := by
    have hdiv := div_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
      (sub_pos.mpr ht.1)) hab
    linarith
  have haff : ContDiff ℝ ∞ (fun t : ℝ => 1 - 2 * (t - a) / (b - a)) :=
    contDiff_const.sub ((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const _)
  exact ((Real.contDiffAt_arccos (ne_of_gt h₁) (ne_of_lt h₂)).comp t
    haff.contDiffAt).contDiffWithinAt




private theorem linearODE_cosine_contDiffOn
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ ∞
      (fun q : P × ℝ => Φ q.1 (cosineClock a b q.2))
      (U ×ˢ Ioo (-1) (Real.pi + 1)) := by
  let : NormedAddCommGroup (G →L[ℝ] G) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (G →L[ℝ] G) := ContinuousLinearMap.toNormedSpace
  let B : P → ℝ → G →L[ℝ] G := fun p s =>
    ((b - a) * Real.sin s / 2) • A p (cosineClock a b s)
  let Ψ := Poincare.ODE.LocalFlow.linearODESolution B (-1) (Real.pi + 1) 0
    (fun p => Φ p a)
  have hzero : (0 : ℝ) ∈ Ioo (-1) (Real.pi + 1) := by
    constructor <;> linarith [Real.pi_pos]
  have harg : ContDiff ℝ ∞ (fun q : P × ℝ => (q.1, cosineClock a b q.2)) :=
    contDiff_fst.prodMk ((cosineClock_contDiff a b).comp contDiff_snd)
  have hcoeff : ContDiffOn ℝ ∞ (fun q : P × ℝ => A q.1 (cosineClock a b q.2))
      (U ×ˢ Ioo (-1) (Real.pi + 1)) :=
    hA.comp harg.contDiffOn (fun q hq => ⟨hq.1, cosineClock_mem hab q.2⟩)
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B)
      (U ×ˢ Ioo (-1) (Real.pi + 1)) :=
    ((contDiffOn_const.mul (Real.contDiff_sin.comp contDiff_snd).contDiffOn).div_const 2).smul
      hcoeff
  have hΨ : ContDiffOn ℝ ∞ (Function.uncurry Ψ)
      (U ×ˢ Ioo (-1) (Real.pi + 1)) :=
    Poincare.ODE.LocalFlow.linearODESolution_contDiffOn_top hzero hU hB hinit
  apply hΨ.congr
  intro q hq
  have hBc : ContinuousOn (B q.1) (Ioo (-1) (Real.pi + 1)) := by
    change ContinuousOn (Function.uncurry B ∘ (fun s : ℝ => (q.1, s))) _
    exact hB.continuousOn.comp
      ((continuous_const.prodMk continuous_id).continuousOn)
      (fun _ hs => ⟨hq.1, hs⟩)
  have hΦ : ∀ s ∈ Ioo (-1) (Real.pi + 1),
      HasDerivAt (fun r => Φ q.1 (cosineClock a b r))
        (B q.1 s (Φ q.1 (cosineClock a b s))) s := by
    intro s _
    change HasDerivAt (fun r => Φ q.1 (cosineClock a b r))
      (((b - a) * Real.sin s / 2) •
        (A q.1 (cosineClock a b s) (Φ q.1 (cosineClock a b s)))) s
    exact (hsol q.1 hq.1 _ (cosineClock_mem hab s)).scomp_hasDerivAt s
        (cosineClock_hasDerivAt a b s) (cosineClock_mem hab)
  have heq := Poincare.ODE.LocalFlow.linearODE_unique_on_Ioo hzero hBc hΦ
    (fun s hs => Poincare.ODE.LocalFlow.linearODESolution_hasDerivAt
      hzero hB.continuousOn hq.1 hs)
    (by
      change Φ q.1 (cosineClock a b 0) = Ψ q.1 0
      rw [show cosineClock a b 0 = a by simp [cosineClock]]
      exact (Poincare.ODE.LocalFlow.linearODESolution_init B (-1) (Real.pi + 1) 0
          (fun p => Φ p a) q.1).symm)
  exact heq hq.2




theorem linearODE_contDiffOn_spatial
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ∞ (fun p => Φ p t) U := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · have hta : t = a := by obtain ⟨ht₁, ht₂⟩ := ht; linarith
    simpa only [hta] using hinit
  let s := cosineClockInv a b t
  have hs : s ∈ Ioo (-1) (Real.pi + 1) := cosineClockInv_mem a b t
  have hclock : cosineClock a b s = t := cosineClock_inv hlt ht
  have harg : ContDiffOn ℝ ∞ (fun p : P => (p, s)) U :=
    contDiffOn_id.prodMk contDiffOn_const
  have hh : ContDiffOn ℝ ∞
      (fun p => Φ p (cosineClock a b s)) U :=
    (linearODE_cosine_contDiffOn A hab hU hA Φ hinit hsol).comp
      harg (fun _ hp => ⟨hp, hs⟩)
  simpa only [hclock] using hh



theorem transportCurveOn_contDiffOn_spatial
    (A : P → ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (hcont : ∀ p, ContinuousOn (A p) (Icc a b)) {K : P → ℝ≥0}
    (hK : ∀ p, ∀ t ∈ Icc a b, ‖A p t‖₊ ≤ K p)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ∞
      (fun p => transportCurveOn (A p) hab (hcont p) (hK p) t) U := by
  apply linearODE_contDiffOn_spatial
    (fun p s => ContinuousLinearMap.compL ℝ V V V (A p s)) hab hU
    ((ContinuousLinearMap.compL ℝ V V V).contDiff.comp_contDiffOn hA)
    (fun p s => transportCurveOn (A p) hab (hcont p) (hK p) s) ?_ ?_ ht
  · apply (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : P => ContinuousLinearMap.id ℝ V) U).congr
    intro p hp
    rw [transportCurveOn_left]
  · intro p hp s hs
    exact transportCurveOn_hasDerivWithinAt (A p) hab (hcont p) (hK p) hs



theorem linearODE_continuousOn
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContinuousOn (Function.uncurry Φ) (U ×ˢ Icc a b) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · have h0 : ContinuousOn (fun q : P × ℝ => Φ q.1 a) (U ×ˢ Icc a b) :=
      hinit.continuousOn.comp continuousOn_fst (fun q hq => hq.1)
    apply h0.congr
    intro q hq
    have ht : q.2 = a := by obtain ⟨ht₁, ht₂⟩ := hq.2; linarith
    simp only [Function.uncurry, ht]
  have harg : Continuous (fun q : P × ℝ => (q.1, cosineClockInv a b q.2)) :=
    continuous_fst.prodMk ((cosineClockInv_continuous a b).comp continuous_snd)
  have hc : ContinuousOn
      (fun q : P × ℝ => Φ q.1 (cosineClock a b (cosineClockInv a b q.2)))
      (U ×ˢ Icc a b) :=
    (linearODE_cosine_contDiffOn A hab hU hA Φ hinit hsol).continuousOn.comp
      harg.continuousOn (fun q hq => ⟨hq.1, cosineClockInv_mem a b q.2⟩)
  exact hc.congr (fun q hq => by
    change Φ q.1 q.2 = Φ q.1 (cosineClock a b (cosineClockInv a b q.2))
    rw [cosineClock_inv hlt hq.2])



theorem linearODE_continuousOn_fderiv_param
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContinuousOn (fun q : P × ℝ => fderiv ℝ (fun p => Φ p q.2) q.1) (U ×ˢ Icc a b) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · have h0 : ContinuousOn (fun q : P × ℝ => fderiv ℝ (fun p => Φ p a) q.1)
        (U ×ˢ Icc a b) :=
      (hinit.fderiv_of_isOpen hU (m := 0) (by simp)).continuousOn.comp
        continuousOn_fst (fun q hq => hq.1)
    apply h0.congr
    intro q hq
    have ht : q.2 = a := by obtain ⟨ht₁, ht₂⟩ := hq.2; linarith
    change fderiv ℝ (fun p => Φ p q.2) q.1 = fderiv ℝ (fun p => Φ p a) q.1
    rw [ht]
  let Ψ : P × ℝ → G := fun q => Φ q.1 (cosineClock a b q.2)
  have hΨ : ContDiffOn ℝ ∞ Ψ (U ×ˢ Ioo (-1) (Real.pi + 1)) :=
    linearODE_cosine_contDiffOn A hab hU hA Φ hinit hsol
  have hopen : IsOpen (U ×ˢ Ioo (-1) (Real.pi + 1)) := hU.prod isOpen_Ioo
  have hD : ContinuousOn
      (fun q => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P ℝ))
      (U ×ˢ Ioo (-1) (Real.pi + 1)) :=
    (hΨ.fderiv_of_isOpen hopen (m := 0) (by simp)).continuousOn.clm_comp
      continuousOn_const
  have harg : Continuous (fun q : P × ℝ => (q.1, cosineClockInv a b q.2)) :=
    continuous_fst.prodMk ((cosineClockInv_continuous a b).comp continuous_snd)
  apply (hD.comp harg.continuousOn
    (fun q hq => ⟨hq.1, cosineClockInv_mem a b q.2⟩)).congr
  intro q hq
  have hpt : (q.1, cosineClockInv a b q.2) ∈ U ×ˢ Ioo (-1) (Real.pi + 1) :=
    ⟨hq.1, cosineClockInv_mem a b q.2⟩
  have hd := ((hΨ _ hpt).contDiffAt (hopen.mem_nhds hpt)).differentiableAt
    (by simp)
  have hc := hd.hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 (cosineClockInv a b q.2))
  have heq : Ψ ∘ (fun p : P => (p, cosineClockInv a b q.2)) = fun p => Φ p q.2 := by
    funext p
    change Φ p (cosineClock a b (cosineClockInv a b q.2)) = Φ p q.2
    rw [cosineClock_inv hlt hq.2]
  rw [heq] at hc
  exact hc.fderiv


theorem linearODE_contDiffOn_interior
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ ∞ (Function.uncurry Φ) (U ×ˢ Ioo a b) := by
  have harg : ContDiffOn ℝ ∞
      (fun q : P × ℝ => (q.1, cosineClockInv a b q.2)) (U ×ˢ Ioo a b) :=
    contDiffOn_fst.prodMk ((cosineClockInv_contDiffOn a b).comp contDiffOn_snd
      (fun _ hq => hq.2))
  have hc : ContDiffOn ℝ ∞
      (fun q : P × ℝ => Φ q.1 (cosineClock a b (cosineClockInv a b q.2)))
      (U ×ˢ Ioo a b) :=
    (linearODE_cosine_contDiffOn A hab hU hA Φ hinit hsol).comp harg
      (fun q hq => ⟨hq.1, cosineClockInv_mem a b q.2⟩)
  apply hc.congr
  intro q hq
  change Φ q.1 q.2 = Φ q.1 (cosineClock a b (cosineClockInv a b q.2))
  rw [cosineClock_inv (hq.2.1.trans hq.2.2) ⟨hq.2.1.le, hq.2.2.le⟩]



theorem linearODE_contDiffOn_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ 1 (Function.uncurry Φ) (U ×ˢ Icc a b) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · have h0 : ContDiffOn ℝ 1 (fun q : P × ℝ => Φ q.1 a) (U ×ˢ Icc a b) :=
      (hinit.of_le (by simp)).comp contDiffOn_fst (fun _ hq => hq.1)
    apply h0.congr
    intro q hq
    have ht : q.2 = a := by obtain ⟨ht₁, ht₂⟩ := hq.2; linarith
    simp only [Function.uncurry, ht]
  let Dx : P × ℝ → P →L[ℝ] G := fun q => fderiv ℝ (fun p => Φ p q.2) q.1
  let Dt : P × ℝ → G := fun q => A q.1 q.2 (Φ q.1 q.2)
  have hDx : ContinuousOn Dx (U ×ˢ Icc a b) :=
    linearODE_continuousOn_fderiv_param A hab hU hA Φ hinit hsol
  have hDt : ContinuousOn Dt (U ×ˢ Icc a b) :=
    hA.continuousOn.clm_apply (linearODE_continuousOn A hab hU hA Φ hinit hsol)
  have hDtL : ContinuousOn (fun q => ContinuousLinearMap.toSpanSingleton ℝ (Dt q))
      (U ×ˢ Icc a b) :=
    ContinuousLinearMap.toSpanSingletonCLE.continuous.comp_continuousOn hDt
  let D : P × ℝ → (P × ℝ) →L[ℝ] G := fun q =>
    (Dx q).coprod (ContinuousLinearMap.toSpanSingleton ℝ (Dt q))
  have hD : ContinuousOn D (U ×ˢ Icc a b) :=
    (ContinuousLinearMap.coprodEquivL ℝ (E := P) (F := ℝ) (G := G)).continuous.comp_continuousOn
      (hDx.prodMk hDtL)
  have hder : ∀ q ∈ U ×ˢ Icc a b,
      HasFDerivWithinAt (Function.uncurry Φ) (D q) (U ×ˢ Icc a b) q := by
    intro q hq
    have hs := linearODE_contDiffOn_spatial A hab hU hA Φ hinit hsol hq.2
    have hx : HasFDerivAt (fun p => Φ p q.2) (Dx q) q.1 :=
      (((hs q.1 hq.1).contDiffAt (hU.mem_nhds hq.1)).differentiableAt (by simp)).hasFDerivAt
    exact Poincare.hasFDerivWithinAt_prod_of_continuous_partial (convex_Icc a b) hq hx
      (fun r hr => (hsol r.1 hr.1 r.2 hr.2).hasFDerivWithinAt) (hDtL q hq)
  have hud : UniqueDiffOn ℝ (U ×ˢ Icc a b) := hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hlt)
  change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (Function.uncurry Φ) (U ×ˢ Icc a b)
  exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hud).mpr
    ⟨by simp, D, contDiffOn_zero.mpr hD, hder⟩

omit [FiniteDimensional ℝ P] in


theorem contDiffOn_fderiv_param_Icc
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b : ℝ} (hab : a < b) {U : Set P} (hU : IsOpen U)
    {f : P × ℝ → G} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Icc a b)) :
    ContDiffOn ℝ ∞ (fun q : P × ℝ => fderiv ℝ (fun p => f (p, q.2)) q.1)
      (U ×ˢ Icc a b) := by
  have hud : UniqueDiffOn ℝ (U ×ˢ Icc a b) := hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hab)
  have hD : ContDiffOn ℝ ∞
      (fun q => (fderivWithin ℝ f (U ×ˢ Icc a b) q).comp (ContinuousLinearMap.inl ℝ P ℝ))
      (U ×ˢ Icc a b) :=
    (hf.fderivWithin hud (m := ∞) (by simp)).clm_comp contDiffOn_const
  apply hD.congr
  intro q hq
  have hprod := (hf.differentiableOn (by simp) q hq).hasFDerivWithinAt
  have hp := hprod.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2).hasFDerivWithinAt
    (fun p hp => (show (p, q.2) ∈ U ×ˢ Icc a b from ⟨hp, hq.2⟩))
  exact (hp.hasFDerivAt (hU.mem_nhds hq.1)).fderiv

end PoincareConjecture.RicciFlow.Frame

end
