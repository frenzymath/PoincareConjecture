import PoincareConjecture.Proofs.M44.Mathlib.ODELinearVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

universe u

theorem tendstoUniformlyOn_ode_spatial_jets
    (m : ℕ) {E P : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {ι : Type*} {l : Filter ι}
    {F : ι → E → E} {G : E → E} {γ : ι → P × ℝ → E} {η : P × ℝ → E}
    {U K : Set P} {I : Set ℝ} {T : ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hT : 0 ≤ T) (hTI : Icc (0 : ℝ) T ⊆ I)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hηsmooth : ContDiffOn ℝ ∞ η (U ×ˢ I))
    (hγsmooth : ∀ᶠ i in l, ContDiffOn ℝ ∞ (γ i) (U ×ˢ I))
    (hγode : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s => γ i (p, s)) (F i (γ i (p, t))) t)
    (hF : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I, ContDiffAt ℝ ∞ (F i) (γ i (p, t)))
    (hηode : ∀ p ∈ U, ∀ t ∈ I,
      HasDerivAt (fun s => η (p, s)) (G (η (p, t))) t)
    (hfield : CompactSmoothConvergenceOn F G l univ)
    (hinitial : CompactSmoothConvergenceOn (fun i p => γ i (p, 0)) (fun p => η (p, 0)) l U) :
    TendstoUniformlyOn
      (fun i (z : P × ℝ) => iteratedFDeriv ℝ m (fun p => γ i (p, z.2)) z.1)
      (fun z : P × ℝ => iteratedFDeriv ℝ m (fun p => η (p, z.2)) z.1)
      l (K ×ˢ Icc (0 : ℝ) T) := by
  induction m generalizing E with
  | zero =>
    have hconv := tendstoUniformlyOn_ode_of_compact_model hT
      (contDiffOn_univ.mp hfield.smooth |>.of_le (by simp)) hK
      (hηsmooth.continuousOn.mono (prod_mono hKU hTI))
      (hγode.mono fun i hi p hp t ht => hi p (hKU hp) t (hTI ht))
      (fun p hp t ht => hηode p (hKU hp) t (hTI ht))
      (fun R => hfield.uniformlyOn (isCompact_closedBall _ R) (subset_univ _))
      (hinitial.uniformlyOn hK hKU)
    have hc := (continuousMultilinearCurryFin0 ℝ P E).symm.isometry.uniformContinuous
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      hc.comp_tendstoUniformlyOn hconv
  | succ m ih =>
    let X := E × (P →L[ℝ] E)
    have hmodel : ContDiffOn ℝ ∞ (linearVariation η) (U ×ˢ I) := by
      intro z hz
      exact (hηsmooth.contDiffAt ((hU.prod hI).mem_nhds hz)).linearVariation.contDiffWithinAt
    have hactual : ∀ᶠ i in l, ContDiffOn ℝ ∞ (linearVariation (γ i)) (U ×ˢ I) := by
      filter_upwards [hγsmooth] with i hi
      intro z hz
      exact (hi.contDiffAt ((hU.prod hI).mem_nhds hz)).linearVariation.contDiffWithinAt
    have hmodelODE : ∀ p ∈ U, ∀ t ∈ I,
        HasDerivAt (fun s => linearVariation η (p, s))
          (linearVariationalField G (linearVariation η (p, t))) t := by
      intro p hp t ht
      exact hasDerivAt_linearVariation
        (hηsmooth.contDiffAt ((hU.prod hI).mem_nhds ⟨hp, ht⟩))
        ((show ∀ᶠ q in 𝓝 p, q ∈ U from hU.mem_nhds hp).mono
          fun q hq => hηode q hq t ht)
        ((contDiffOn_univ.mp hfield.smooth).differentiable (by simp) _)
    have hactualODE : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I,
        HasDerivAt (fun s => linearVariation (γ i) (p, s))
          (linearVariationalField (F i) (linearVariation (γ i) (p, t))) t := by
      filter_upwards [hγsmooth, hγode, hF] with i his hio hif
      intro p hp t ht
      exact hasDerivAt_linearVariation
        (his.contDiffAt ((hU.prod hI).mem_nhds ⟨hp, ht⟩))
        ((show ∀ᶠ q in 𝓝 p, q ∈ U from hU.mem_nhds hp).mono
          fun q hq => hio q hq t ht)
        ((hif p hp t ht).differentiableAt (by simp))
    have hactualField : ∀ᶠ i in l, ∀ p ∈ U, ∀ t ∈ I,
        ContDiffAt ℝ ∞ (linearVariationalField (F i)) (linearVariation (γ i) (p, t)) := by
      filter_upwards [hF] with i hi
      exact fun p hp t ht => (hi p hp t ht).linearVariationalField
    have hconv := ih (E := X) hmodel hactual hactualODE hactualField hmodelODE
      hfield.linearVariationalField (hinitial.prodMk hinitial.fderiv)
    let L := ContinuousLinearMap.snd ℝ E (P →L[ℝ] E)
    have hread : UniformContinuous
        (fun J : P [×m]→L[ℝ] X => L.compContinuousMultilinearMap J) :=
      uniformContinuous_snd.comp
        (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin m => P)
          E (P →L[ℝ] E)).symm.isometry.uniformContinuous
    have hproject := hread.comp_tendstoUniformlyOn hconv
    have hderivative : TendstoUniformlyOn
        (fun i (z : P × ℝ) => iteratedFDeriv ℝ m
          (fderiv ℝ (fun p => γ i (p, z.2))) z.1)
        (fun z : P × ℝ => iteratedFDeriv ℝ m
          (fderiv ℝ (fun p => η (p, z.2))) z.1) l (K ×ˢ Icc (0 : ℝ) T) := by
      apply (hproject.congr ?_).congr_right ?_
      · filter_upwards [hactual] with i hi
        intro z hz
        have hs := (hi.contDiffAt ((hU.prod hI).mem_nhds ⟨hKU hz.1, hTI hz.2⟩)).comp
          z.1 (contDiffAt_id.prodMk contDiffAt_const)
        exact (L.iteratedFDeriv_comp_left hs (by exact_mod_cast le_top)).symm
      · intro z hz
        have hs := (hmodel.contDiffAt ((hU.prod hI).mem_nhds ⟨hKU hz.1, hTI hz.2⟩)).comp
          z.1 (contDiffAt_id.prodMk contDiffAt_const)
        exact (L.iteratedFDeriv_comp_left hs (by exact_mod_cast le_top)).symm
    have hc := (continuousMultilinearCurryRightEquiv' ℝ m P E).symm.isometry.uniformContinuous
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def] using
      hc.comp_tendstoUniformlyOn hderivative
