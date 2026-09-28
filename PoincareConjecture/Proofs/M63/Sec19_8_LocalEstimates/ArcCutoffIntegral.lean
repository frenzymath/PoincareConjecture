import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffTime
import PoincareConjecture.Proofs.M62.Cor0_3_RegularizedEvolution
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem m63ArcLength_joint_continuousOn (hc : M62ShrinkingCurve F c) (x0 : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m63ArcLength F c z.2 x0 z.1)
      (univ ×ˢ Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (z : univ ×ˢ Icc a b) y => curveSpeed F c z.val.2 y)
    ((speed_continuousOn F c hc).comp_continuous
      (continuous_snd.prodMk
        ((continuous_snd.comp continuous_subtype_val).comp continuous_fst))
      (fun z => ⟨mem_univ _, z.1.property.2⟩))
    (continuous_fst.comp continuous_subtype_val)

theorem m63ArcCutoff_regularizedIntegral_time_regular (hc : M62ShrinkingCurve F c)
    (alpha beta x0 r : ℝ) {ε : ℝ} (hε : 0 < ε)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi) :
    let Z : ℝ × ℝ → ℝ := fun z => psi (m63ArcLength F c z.2 x0 z.1 / r) *
      m62RegularizedCurvature F c ε z.2 z.1 * curveSpeed F c z.2 z.1
    let Zt : ℝ × ℝ → ℝ := fun z => deriv (fun tau => Z (z.1, tau)) z.2
    let I : ℝ → ℝ := fun t => ∫ x in alpha..beta, Z (x, t)
    ContinuousOn I (Icc a b) ∧
      ContinuousOn Zt (univ ×ˢ Ioo a b) ∧
      (∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun tau => Z (x, tau)) (Zt (x, t)) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt I (∫ x in alpha..beta, Zt (x, t)) t) := by
  dsimp only
  let sigma : ℝ × ℝ → ℝ := fun z => m63ArcLength F c z.2 x0 z.1
  let phi : ℝ × ℝ → ℝ := fun z => psi (sigma z / r)
  let H : ℝ × ℝ → ℝ := fun z =>
    m62RegularizedCurvature F c ε z.2 z.1 * curveSpeed F c z.2 z.1
  let Z : ℝ × ℝ → ℝ := fun z => phi z *
    m62RegularizedCurvature F c ε z.2 z.1 * curveSpeed F c z.2 z.1
  let Zt : ℝ × ℝ → ℝ := fun z => deriv (fun tau => Z (z.1, tau)) z.2
  let I : ℝ → ℝ := fun t => ∫ x in alpha..beta, Z (x, t)
  change ContinuousOn I (Icc a b) ∧ ContinuousOn Zt (univ ×ˢ Ioo a b) ∧
    (∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun tau => Z (x, tau)) (Zt (x, t)) t) ∧
    (∀ t ∈ Ioo a b, HasDerivAt I (∫ x in alpha..beta, Zt (x, t)) t)
  have hsigma : ContinuousOn sigma (univ ×ˢ Icc a b) :=
    m63ArcLength_joint_continuousOn F c hc x0
  have hphi : ContinuousOn phi (univ ×ˢ Icc a b) :=
    hpsi.continuous.comp_continuousOn (hsigma.div_const r)
  have hZ : ContinuousOn Z (univ ×ˢ Icc a b) :=
    (hphi.mul (regularized_continuousOn F c hc ε)).mul (speed_continuousOn F c hc)
  have hI : ContinuousOn I (Icc a b) := hZ.intervalIntegral_prod_left alpha beta
  have hsub : univ ×ˢ Ioo a b ⊆ (univ ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    prod_mono Subset.rfl Ioo_subset_Icc_self
  let V : ℝ × ℝ → ℝ := fun z => curveSpeed F c z.2 z.1
  let Vt := M08.variationParameterDeriv univ (Ioo a b) V
  have hV : ContDiffOn ℝ ∞ V (univ ×ˢ Ioo a b) := speed_joint_contDiffOn F c hc
  have hVt : ContDiffOn ℝ ∞ Vt (univ ×ˢ Ioo a b) :=
    M08.variationParameterDeriv_contDiffOn uniqueDiffOn_univ isOpen_Ioo V hV
  have hVtime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun tau => V (x, tau)) (Vt (x, t)) t :=
    M08.hasDerivAt_variationParameter isOpen_Ioo V hV (mem_univ x) ht
  have hVlaw (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      Vt (x, t) = -(m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
        curveSpeed F c t x := by
    calc
      _ = -(m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
          curveSpeed F c t x := (hVtime t ht x).unique (hasDerivAt_speed F c hc ht x)
      _ = _ := by ring
  let sigmaT : ℝ × ℝ → ℝ := fun z => ∫ y in x0..z.1, Vt (y, z.2)
  have hsigmaT : ContinuousOn sigmaT (univ ×ˢ Ioo a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (z : univ ×ˢ Ioo a b) y => Vt (y, z.val.2))
      (hVt.continuousOn.comp_continuous
        (continuous_snd.prodMk
          ((continuous_snd.comp continuous_subtype_val).comp continuous_fst))
        (fun z => ⟨mem_univ _, z.1.property.2⟩))
      (continuous_fst.comp continuous_subtype_val)
  have hsigmaTime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun tau => sigma (x, tau)) (sigmaT (x, t)) t := by
    apply (m63SignedArcLength_hasDerivAt F c hc x0 x ht).congr_deriv
    change -(∫ y in x0..x,
      (m62CurvatureSquared F c t y + m62TangentRicci F c t y) * curveSpeed F c t y) =
        ∫ y in x0..x, Vt (y, t)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _hy
    simpa only [neg_mul] using (hVlaw t ht y).symm
  let phiT : ℝ × ℝ → ℝ := fun z => (deriv psi (sigma z / r) / r) * sigmaT z
  have hphiT : ContinuousOn phiT (univ ×ˢ Ioo a b) :=
    (((hpsi.continuous_deriv (by norm_num)).comp_continuousOn
      ((hsigma.mono hsub).div_const r)).div_const r).mul hsigmaT
  have hphiTime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun tau => phi (x, tau)) (phiT (x, t)) t := by
    apply (((hpsi.differentiable (by norm_num)) (sigma (x, t) / r)).hasDerivAt.comp t
      ((hsigmaTime t ht x).div_const r)).congr_deriv
    dsimp only [phiT]
    ring
  have hH : ContDiffOn ℝ ∞ H (univ ×ˢ Ioo a b) :=
    (regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).mul hV
  let Ht := M08.variationParameterDeriv univ (Ioo a b) H
  have hHt : ContDiffOn ℝ ∞ Ht (univ ×ˢ Ioo a b) :=
    M08.variationParameterDeriv_contDiffOn uniqueDiffOn_univ isOpen_Ioo H hH
  have hHtime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun tau => H (x, tau)) (Ht (x, t)) t :=
    M08.hasDerivAt_variationParameter isOpen_Ioo H hH (mem_univ x) ht
  let Z' : ℝ × ℝ → ℝ := fun z => phiT z * H z + phi z * Ht z
  have hZ' : ContinuousOn Z' (univ ×ˢ Ioo a b) :=
    (hphiT.mul hH.continuousOn).add ((hphi.mono hsub).mul hHt.continuousOn)
  have hZtime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun tau => Z (x, tau)) (Z' (x, t)) t := by
    simpa only [Z, Z', H, mul_assoc] using (hphiTime t ht x).fun_mul (hHtime t ht x)
  have hZt : ContinuousOn Zt (univ ×ˢ Ioo a b) :=
    hZ'.congr fun z hz => (hZtime z.2 hz.2 z.1).deriv
  refine ⟨hI, hZt, fun t ht x => (hZtime t ht x).differentiableAt.hasDerivAt, ?_⟩
  intro t ht
  have hslice (s : ℝ) (hs : s ∈ Ioo a b) : Continuous (fun x => Z (x, s)) :=
    hZ.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, Ioo_subset_Icc_self hs⟩)
  have hsliceT (s : ℝ) (hs : s ∈ Ioo a b) : Continuous (fun x => Zt (x, s)) :=
    hZt.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hs⟩)
  obtain ⟨l, u, _htu, hnear, hinside⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
  obtain ⟨K, hK⟩ :=
    (isCompact_uIcc.prod (isCompact_Icc : IsCompact (Icc l u))).exists_bound_of_continuousOn
      (hZt.mono (prod_mono (subset_univ (uIcc alpha beta)) hinside))
  change HasDerivAt (fun s => ∫ x in alpha..beta, Z (x, s))
    (∫ x in alpha..beta, Zt (x, t)) t
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => Z (x, s)) (F' := fun s x => Zt (x, s))
    (bound := fun _ => K) hnear ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((hslice s hs).intervalIntegrable _ _).aestronglyMeasurable_restrict_uIoc
  · exact (hslice t ht).intervalIntegrable _ _
  · exact ((hsliceT t ht).intervalIntegrable _ _).aestronglyMeasurable_restrict_uIoc
  · exact Eventually.of_forall fun x hx s hs => hK (x, s) ⟨uIoc_subset_uIcc hx, hs⟩
  · exact Eventually.of_forall fun x _hx s hs =>
      (hZtime s (hinside hs) x).differentiableAt.hasDerivAt

end PoincareConjecture
