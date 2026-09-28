import PoincareConjecture.Proofs.M44.Mathlib.UniformCompactDerivative
import PoincareConjecture.Proofs.M44.Mathlib.ODEModelBuffer
import PoincareConjecture.Proofs.M07.Analysis.Calculus.MixedDerivatives











set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

section FirstVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def firstVariationalField (F : E → E) (z : E × E) : E × E :=
  (F z.1, fderiv ℝ F z.1 z.2)


theorem ContDiff.firstVariationalField {F : E → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (firstVariationalField F) :=
  (hF.comp contDiff_fst).prodMk
    (((hF.fderiv_right (m := ∞) (by simp)).comp contDiff_fst).clm_apply contDiff_snd)



theorem hasDerivAt_first_variation
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : E → E} {γ : P × ℝ → E} {p : P} {t : ℝ}
    (hγ : ContDiffAt ℝ ∞ γ (p, t))
    (hode : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => γ (q, s)) (F (γ (q, t))) t)
    (hF : DifferentiableAt ℝ F (γ (p, t))) (v : P) :
    HasDerivAt
      (fun s => (γ (p, s), fderiv ℝ (fun q => γ (q, s)) p v))
      (firstVariationalField F (γ (p, t), fderiv ℝ (fun q => γ (q, t)) p v)) t := by
  have hswap : ContDiffAt ℝ ∞ (fun z : ℝ × P => γ (z.2, z.1)) (t, p) :=
    hγ.comp (t, p) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hd := Poincare.Analysis.hasDerivAt_fderiv_time_of_eventually hswap hode v
  have hspace : DifferentiableAt ℝ (fun q => γ (q, t)) p :=
    (hγ.comp p (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hchain := fderiv_comp p hF hspace
  change fderiv ℝ (fun q => F (γ (q, t))) p =
    (fderiv ℝ F (γ (p, t))).comp (fderiv ℝ (fun q => γ (q, t)) p) at hchain
  rw [hchain] at hd
  exact hode.self_of_nhds.prodMk hd



theorem tendstoUniformlyOn_firstVariationalField
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι}
    {F : ι → E → E} {G : E → E} (hG : ContDiff ℝ 1 G)
    {K V : Set E} (hK : IsCompact K) (hV : IsCompact V)
    (hzero : TendstoUniformlyOn F G l K)
    (hone : TendstoUniformlyOn (fun i => fderiv ℝ (F i)) (fderiv ℝ G) l K) :
    TendstoUniformlyOn (fun i => firstVariationalField (F i))
      (firstVariationalField G) l (K ×ˢ V) := by
  let H (z : E × (E →L[ℝ] E) × E) : E × E := (z.1, z.2.1 z.2.2)
  have hH : Continuous H := by dsimp [H]; fun_prop
  have h0 := (hzero.comp Prod.fst).mono (fun _ hz => hz.1 : K ×ˢ V ⊆ Prod.fst ⁻¹' K)
  have h1 := (hone.comp Prod.fst).mono (fun _ hz => hz.1 : K ×ˢ V ⊆ Prod.fst ⁻¹' K)
  have hv : TendstoUniformlyOn (fun _ : ι => (Prod.snd : E × E → E)) Prod.snd l (K ×ˢ V) :=
    Metric.tendstoUniformlyOn_iff.mpr fun epsilon hepsilon =>
      Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hepsilon
  have hJ : Continuous (fun z : E × E => (G z.1, fderiv ℝ G z.1, z.2)) :=
    (hG.continuous.comp continuous_fst).prodMk
      ((((hG.fderiv_right (m := 0) (by simp)).continuous).comp continuous_fst).prodMk
        continuous_snd)
  exact hH.continuousOn.comp_tendstoUniformlyOn_of_compact_image isOpen_univ
    ((hK.prod hV).image hJ) (fun _ _ => mem_univ _) (h0.prodMk_same (h1.prodMk_same hv))

end FirstVariation

section SolutionFamilies

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]



noncomputable def firstVariation (γ : P × ℝ → E) (z : P × P) (t : ℝ) : E × E :=
  (γ (z.1, t), fderiv ℝ (fun p => γ (p, t)) z.1 z.2)



theorem ContDiffAt.firstVariation {γ : P × ℝ → E} {p v : P} {t : ℝ}
    (hγ : ContDiffAt ℝ ∞ γ (p, t)) :
    ContDiffAt ℝ ∞ (fun z : (P × P) × ℝ => firstVariation γ z.1 z.2) ((p, v), t) := by
  have harg : ContDiff ℝ ∞ (fun z : (P × P) × ℝ => (z.1.1, z.2)) := by fun_prop
  have hdir : ContDiff ℝ ∞ (fun z : (P × P) × ℝ => (z.1.2, (0 : ℝ))) := by fun_prop
  have hformula : ContDiffAt ℝ ∞
      (fun z : (P × P) × ℝ =>
        (γ (z.1.1, z.2), fderiv ℝ γ (z.1.1, z.2) (z.1.2, 0))) ((p, v), t) :=
    (hγ.comp (f := fun z : (P × P) × ℝ => (z.1.1, z.2)) ((p, v), t)
      harg.contDiffAt).prodMk
      (((hγ.fderiv_right (m := ∞) (by simp)).comp
        (f := fun z : (P × P) × ℝ => (z.1.1, z.2)) ((p, v), t)
          harg.contDiffAt).clm_apply hdir.contDiffAt)
  have hnear : ∀ᶠ q in 𝓝 (p, t), DifferentiableAt ℝ γ q :=
    ((hγ.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by decide)).mono
      (fun _ h => h.differentiableAt one_ne_zero)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [harg.continuous.continuousAt.eventually hnear] with z hz
  change DifferentiableAt ℝ γ (z.1.1, z.2) at hz
  have hinc : HasFDerivAt (fun q : P => (q, z.2))
      ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] ℝ)) z.1.1 := by
    exact (hasFDerivAt_id (𝕜 := ℝ) z.1.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1.1)
  have hspace := hz.hasFDerivAt.comp z.1.1 hinc
  change (γ (z.1.1, z.2), fderiv ℝ (fun p => γ (p, z.2)) z.1.1 z.1.2) = _
  refine Prod.ext rfl ?_
  simpa only [firstVariation, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using congrArg (fun D => D z.1.2) hspace.fderiv




theorem tendstoUniformlyOn_firstVariation_of_compact_model
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι}
    {F : ι → E → E} {G : E → E} {γ : ι → P × ℝ → E} {η : P × ℝ → E}
    {U K V : Set P} {I : Set ℝ} {T : ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hT : 0 ≤ T) (hTI : Icc (0 : ℝ) T ⊆ I)
    (hK : IsCompact K) (hV : IsCompact V) (hKU : K ⊆ U)
    (hG : ContDiff ℝ ∞ G) (hηsmooth : ContDiffOn ℝ ∞ η (U ×ˢ I))
    (hγsmooth : ∀ᶠ i in l, ContDiffOn ℝ ∞ (γ i) (U ×ˢ I))
    (hγode : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s => γ i (p, s)) (F i (γ i (p, t))) t)
    (hF : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I, DifferentiableAt ℝ (F i) (γ i (p, t)))
    (hηode : ∀ p ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s => η (p, s)) (G (η (p, t))) t)
    (hzero : ∀ R : ℝ, TendstoUniformlyOn F G l (closedBall 0 R))
    (hone : ∀ R : ℝ, TendstoUniformlyOn (fun i => fderiv ℝ (F i))
      (fderiv ℝ G) l (closedBall 0 R))
    (hinitial : TendstoUniformlyOn (fun i z => firstVariation (γ i) z 0)
      (fun z => firstVariation η z 0) l (K ×ˢ V)) :
    TendstoUniformlyOn (fun i (z : (P × P) × ℝ) => firstVariation (γ i) z.1 z.2)
      (fun z => firstVariation η z.1 z.2) l ((K ×ˢ V) ×ˢ Icc (0 : ℝ) T) := by
  have hmodel : ContinuousOn (fun z : (P × P) × ℝ => firstVariation η z.1 z.2)
      ((K ×ˢ V) ×ˢ Icc (0 : ℝ) T) := by
    intro z hz
    exact ((hηsmooth.contDiffAt
      ((hU.prod hI).mem_nhds ⟨hKU hz.1.1, hTI hz.2⟩)).firstVariation
        (v := z.1.2)).continuousAt.continuousWithinAt
  have hmodelODE : ∀ z ∈ K ×ˢ V, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (firstVariation η z)
        (firstVariationalField G (firstVariation η z t)) t := by
    intro z hz t ht
    exact hasDerivAt_first_variation
      (hηsmooth.contDiffAt ((hU.prod hI).mem_nhds ⟨hKU hz.1, hTI ht⟩))
      ((show ∀ᶠ p in 𝓝 z.1, p ∈ U from hU.mem_nhds (hKU hz.1)).mono
        (fun p hp => hηode p hp t (hTI ht)))
      (hG.differentiable (by simp) _) z.2
  have hactualODE : ∀ᶠ i in l, ∀ z ∈ K ×ˢ V, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (firstVariation (γ i) z)
        (firstVariationalField (F i) (firstVariation (γ i) z t)) t := by
    filter_upwards [hγsmooth, hγode, hF] with i his hio hif
    intro z hz t ht
    exact hasDerivAt_first_variation
      (his.contDiffAt ((hU.prod hI).mem_nhds ⟨hKU hz.1, hTI ht⟩))
      ((show ∀ᶠ p in 𝓝 z.1, p ∈ U from hU.mem_nhds (hKU hz.1)).mono
        (fun p hp => hio p hp t (hTI ht)))
      (hif z.1 (hKU hz.1) t (hTI ht)) z.2
  have hfield : ∀ R : ℝ,
      TendstoUniformlyOn (fun i => firstVariationalField (F i))
        (firstVariationalField G) l (closedBall (0 : E × E) R) := by
    intro R
    rw [show (0 : E × E) = (0, 0) from rfl, ← closedBall_prod_same]
    exact tendstoUniformlyOn_firstVariationalField (hG.of_le (by simp))
      (isCompact_closedBall _ _) (isCompact_closedBall _ _) (hzero R) (hone R)
  exact tendstoUniformlyOn_ode_of_compact_model hT
    (hG.firstVariationalField.of_le (by simp)) (hK.prod hV) hmodel
    hactualODE hmodelODE hfield hinitial

end SolutionFamilies
