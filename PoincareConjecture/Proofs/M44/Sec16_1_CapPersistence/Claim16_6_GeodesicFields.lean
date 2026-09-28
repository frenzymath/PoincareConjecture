import PoincareConjecture.Proofs.M44.Mathlib.UniformCompactComposition
import PoincareConjecture.Proofs.M44.Mathlib.UniformCompactDerivative
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialJetConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

universe u

namespace PoincareConjecture.M44

section GeodesicOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Trilin" => E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
local notation "Jet" => Bilin × Trilin × E

noncomputable local instance : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance : NormedAddCommGroup Trilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ Trilin :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def geodesicFieldJet (J : Jet) : E × E :=
  (J.2.2, -J.1.inverse (metricKoszulCovector J.2.1 J.2.2 J.2.2))

private theorem contDiffAt_geodesicFieldJet {J : Jet} (hJ : J.1.IsInvertible) :
    ContDiffAt ℝ ∞ (geodesicFieldJet (E := E)) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : Jet => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  have hflip : ContDiff ℝ ∞ (fun L : Bilin => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hflip' : ContDiff ℝ ∞ (fun L : Trilin => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  have hK : ContDiffAt ℝ ∞
      (fun K : Jet => metricKoszulCovector K.2.1 K.2.2 K.2.2) J := by
    unfold metricKoszulCovector
    fun_prop
  exact (contDiffAt_snd.comp J contDiffAt_snd).prodMk (hI.clm_apply hK).neg




theorem compactSmoothConvergenceOn_geodesicField
    {ι : Type*} {l : Filter ι} {Bseq : ι → E → Bilin} {B : E → Bilin}
    (h : CompactSmoothConvergenceOn Bseq B l univ) (hinv : ∀ x, (B x).IsInvertible) :
    CompactSmoothConvergenceOn (fun i => coordinateGeodesicField (Bseq i))
      (coordinateGeodesicField B) l univ := by
  have h0 : CompactSmoothConvergenceOn (fun i (z : E × E) => Bseq i z.1)
      (fun z => B z.1) l univ := by
    simpa only [preimage_univ, Function.comp_def, ContinuousLinearMap.coe_fst'] using
      h.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ E E)
  have h1 : CompactSmoothConvergenceOn (fun i (z : E × E) => fderiv ℝ (Bseq i) z.1)
      (fun z => fderiv ℝ B z.1) l univ := by
    simpa only [preimage_univ, Function.comp_def, ContinuousLinearMap.coe_fst'] using
      h.fderiv.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ E E)
  have hv : CompactSmoothConvergenceOn (fun _ : ι => (Prod.snd : E × E → E))
      Prod.snd l univ :=
    CompactSmoothConvergenceOn.constant isOpen_univ contDiff_snd.contDiffOn
  let U : Set Jet := {J | J.1.IsInvertible}
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage continuous_fst
  have houter : ContDiffOn ℝ ∞ (geodesicFieldJet (E := E)) U :=
    fun J hJ => (contDiffAt_geodesicFieldJet hJ).contDiffWithinAt
  exact (h0.prodMk (h1.prodMk hv)).comp_smooth hU houter (fun z _ => hinv z.1)




theorem tendstoUniformlyOn_geodesicField_of_coefficients
    {ι : Type*} {l : Filter ι} {Bseq : ι → E → Bilin} {B : E → Bilin}
    (hB : ContDiff ℝ ∞ B) (hinv : ∀ x, (B x).IsInvertible)
    {K V : Set E} (hK : IsCompact K) (hV : IsCompact V)
    (hzero : TendstoUniformlyOn Bseq B l K)
    (hone : TendstoUniformlyOn (fun i => fderiv ℝ (Bseq i)) (fderiv ℝ B) l K) :
    TendstoUniformlyOn (fun i => coordinateGeodesicField (Bseq i))
      (coordinateGeodesicField B) l (K ×ˢ V) := by
  let U : Set Jet := {J | J.1.IsInvertible}
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage continuous_fst
  have hoperator : ContinuousOn (geodesicFieldJet (E := E)) U :=
    fun J hJ => (contDiffAt_geodesicFieldJet hJ).continuousAt.continuousWithinAt
  let F (i : ι) (z : E × E) : Jet := (Bseq i z.1, fderiv ℝ (Bseq i) z.1, z.2)
  let G (z : E × E) : Jet := (B z.1, fderiv ℝ B z.1, z.2)
  have hG : Continuous G :=
    (hB.continuous.comp continuous_fst).prodMk
      (((hB.fderiv_right (m := ∞) (by simp)).continuous.comp continuous_fst).prodMk continuous_snd)
  have hF0 : TendstoUniformlyOn (fun i (z : E × E) => Bseq i z.1)
      (fun z => B z.1) l (K ×ˢ V) :=
    (hzero.comp Prod.fst).mono (fun _ hz => hz.1)
  have hF1 : TendstoUniformlyOn (fun i (z : E × E) => fderiv ℝ (Bseq i) z.1)
      (fun z => fderiv ℝ B z.1) l (K ×ˢ V) :=
    (hone.comp Prod.fst).mono (fun _ hz => hz.1)
  have hvel : TendstoUniformlyOn (fun _ : ι => (Prod.snd : E × E → E)) Prod.snd l (K ×ˢ V) :=
    Metric.tendstoUniformlyOn_iff.mpr fun epsilon hepsilon =>
      Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hepsilon
  have hfirst : TendstoUniformlyOn
      (fun i (z : E × E) => (fderiv ℝ (Bseq i) z.1, z.2))
      (fun z => (fderiv ℝ B z.1, z.2)) l (K ×ˢ V) := by
    intro u hu
    exact (tendsto_id.prodMk tendsto_id).eventually ((hF1.prodMk hvel) u hu)
  have hFG : TendstoUniformlyOn F G l (K ×ˢ V) := by
    intro u hu
    exact (tendsto_id.prodMk tendsto_id).eventually ((hF0.prodMk hfirst) u hu)
  exact hoperator.comp_tendstoUniformlyOn_of_compact_image hU
    ((hK.prod hV).image hG) (fun z _ => hinv z.1) hFG

set_option maxHeartbeats 800000 in




theorem tendstoUniformlyOn_fderiv_geodesicField_of_coefficients
    {ι : Type*} {l : Filter ι} {Bseq : ι → E → Bilin} {B : E → Bilin}
    (hB : ContDiff ℝ ∞ B) (hinv : ∀ x, (B x).IsInvertible)
    {K V : Set E} (hK : IsCompact K) (hV : IsCompact V)
    (hBseq : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (Bseq i) x)
    (hzero : TendstoUniformlyOn Bseq B l K)
    (hone : TendstoUniformlyOn (fun i => fderiv ℝ (Bseq i)) (fderiv ℝ B) l K)
    (htwo : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (Bseq i)))
      (fderiv ℝ (fderiv ℝ B)) l K) :
    TendstoUniformlyOn (fun i => fderiv ℝ (coordinateGeodesicField (Bseq i)))
      (fderiv ℝ (coordinateGeodesicField B)) l (K ×ˢ V) := by
  let J (C : E → Bilin) (z : E × E) : Jet := (C z.1, fderiv ℝ C z.1, z.2)
  let D (p : Trilin × (E →L[ℝ] Trilin)) : (E × E) →L[ℝ] Jet :=
    (p.1.comp (ContinuousLinearMap.fst ℝ E E)).prod
      ((p.2.comp (ContinuousLinearMap.fst ℝ E E)).prod (ContinuousLinearMap.snd ℝ E E))
  have hD : Continuous D := by
    have hfirst : Continuous (fun p : Trilin × (E →L[ℝ] Trilin) =>
        p.1.comp (ContinuousLinearMap.fst ℝ E E)) := continuous_fst.clm_comp_const _
    have hsecond : Continuous (fun p : Trilin × (E →L[ℝ] Trilin) =>
        p.2.comp (ContinuousLinearMap.fst ℝ E E)) := continuous_snd.clm_comp_const _
    have hpair : Continuous (fun p : Trilin × (E →L[ℝ] Trilin) =>
        (p.2.comp (ContinuousLinearMap.fst ℝ E E)).prod (ContinuousLinearMap.snd ℝ E E)) :=
      (ContinuousLinearMap.prodₗᵢ ℝ (𝕜 := ℝ) (E := E × E) (F := Trilin) (G := E)).continuous.comp
        (hsecond.prodMk continuous_const)
    exact (ContinuousLinearMap.prodₗᵢ ℝ (𝕜 := ℝ) (E := E × E)
      (F := Bilin) (G := Trilin × E)).continuous.comp (hfirst.prodMk hpair)
  have hDJ {C : E → Bilin} {z : E × E} (hC : ContDiffAt ℝ ∞ C z.1) :
      HasFDerivAt (J C)
        (D (fderiv ℝ C z.1, fderiv ℝ (fderiv ℝ C) z.1)) z := by
    exact ((hC.differentiableAt (by simp)).hasFDerivAt.comp z hasFDerivAt_fst).prodMk
      ((((hC.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp
        z hasFDerivAt_fst).prodMk hasFDerivAt_snd)
  have hJ : ContDiff ℝ ∞ (J B) :=
    (hB.comp contDiff_fst).prodMk
      (((hB.fderiv_right (m := ∞) (by simp)).comp contDiff_fst).prodMk contDiff_snd)
  have hJ0 : TendstoUniformlyOn (fun i => J (Bseq i)) (J B) l (K ×ˢ V) := by
    have h0 := (hzero.comp Prod.fst).mono (fun _ hz => hz.1 : K ×ˢ V ⊆ Prod.fst ⁻¹' K)
    have h1 := (hone.comp Prod.fst).mono (fun _ hz => hz.1 : K ×ˢ V ⊆ Prod.fst ⁻¹' K)
    have hv : TendstoUniformlyOn (fun _ : ι => (Prod.snd : E × E → E)) Prod.snd l (K ×ˢ V) :=
      Metric.tendstoUniformlyOn_iff.mpr fun epsilon hepsilon =>
        Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hepsilon
    exact h0.prodMk_same (h1.prodMk_same hv)
  have hpair : TendstoUniformlyOn
      (fun i (z : E × E) => (fderiv ℝ (Bseq i) z.1, fderiv ℝ (fderiv ℝ (Bseq i)) z.1))
      (fun z : E × E => (fderiv ℝ B z.1, fderiv ℝ (fderiv ℝ B) z.1)) l (K ×ˢ V) :=
    ((hone.prodMk_same htwo).comp Prod.fst).mono (fun _ hz => hz.1)
  have hdB : ContDiff ℝ ∞ (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hddB : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ B)) := hdB.fderiv_right (by simp)
  have hpcont : Continuous
      (fun z : E × E => (fderiv ℝ B z.1, fderiv ℝ (fderiv ℝ B) z.1)) :=
    (hdB.continuous.comp continuous_fst).prodMk (hddB.continuous.comp continuous_fst)
  have hJD := hD.continuousOn.comp_tendstoUniformlyOn_of_compact_image isOpen_univ
    ((hK.prod hV).image hpcont) (fun _ _ => mem_univ _) hpair
  have hJ1 : TendstoUniformlyOn (fun i => fderiv ℝ (J (Bseq i))) (fderiv ℝ (J B))
      l (K ×ˢ V) := by
    rw [Metric.tendstoUniformlyOn_iff] at hJD ⊢
    intro epsilon hepsilon
    filter_upwards [hBseq, hJD epsilon hepsilon] with i hi herr
    intro z hz
    have hiD : fderiv ℝ (J (Bseq i)) z =
        D (fderiv ℝ (Bseq i) z.1, fderiv ℝ (fderiv ℝ (Bseq i)) z.1) :=
      (hDJ (C := Bseq i) (z := z) (hi z.1 hz.1)).fderiv
    have hmD : fderiv ℝ (J B) z = D (fderiv ℝ B z.1, fderiv ℝ (fderiv ℝ B) z.1) :=
      (hDJ (C := B) (z := z) hB.contDiffAt).fderiv
    rw [hiD, hmD]
    exact herr z hz
  let U : Set Jet := {z | z.1.IsInvertible}
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage continuous_fst
  have houter : ContDiffOn ℝ 1 (geodesicFieldJet (E := E)) U := fun z hz =>
    ((contDiffAt_geodesicFieldJet hz).of_le (by simp)).contDiffWithinAt
  exact tendstoUniformlyOn_fderiv_comp_of_compact (hK.prod hV) hU
    (fun _ _ => hJ.contDiffAt.of_le (by simp)) houter (fun z _ => hinv z.1)
    (hBseq.mono fun i hi z hz => (hDJ (hi z.1 hz.1)).differentiableAt) hJ0 hJ1

end GeodesicOperator

section ActualComparisons

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace




theorem compactSmoothConvergenceOn_initial_coefficients
    (g₀ : StandardInitialMetric)
    (S : ℕ → GeneralizedSliceCarrier.{u})
    (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
    (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ)
    (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
    (heta : Tendsto eta atTop (𝓝 0)) :
    CompactSmoothConvergenceOn (fun n => (Q n).normalizedCoefficients)
      g₀.metric.euclideanCoefficients atTop univ where
  isOpen := isOpen_univ
  smooth := (contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients).contDiffOn
  eventually_smooth K hK _ := by
    obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g₀ hK 0
    filter_upwards [heta.eventually (gt_mem_nhds hdelta)] with n hn
    intro x hx
    exact (Q n).contDiffOn_normalizedCoefficients.contDiffAt
      ((Q n).toPartialDiffeomorph.open_source.mem_nhds
        ((hdomain (eta n) (Q n).eta_pos hn.le).2 hx))
  jets j _ hK _ := tendstoUniformlyOn_initial_coefficient_jets g₀ S g tip scale eta Q heta j hK



theorem compactSmoothConvergenceOn_initial_geodesicFields
    (g₀ : StandardInitialMetric)
    (S : ℕ → GeneralizedSliceCarrier.{u})
    (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
    (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ)
    (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
    (heta : Tendsto eta atTop (𝓝 0)) :
    CompactSmoothConvergenceOn (fun n => coordinateGeodesicField (Q n).normalizedCoefficients)
      (coordinateGeodesicField g₀.metric.euclideanCoefficients) atTop univ :=
  compactSmoothConvergenceOn_geodesicField
    (compactSmoothConvergenceOn_initial_coefficients g₀ S g tip scale eta Q heta)
    g₀.metric.inner_isInvertible



theorem tendstoUniformlyOn_initial_geodesicFields
    (g₀ : StandardInitialMetric)
    (S : ℕ → GeneralizedSliceCarrier.{u})
    (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
    (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ)
    (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
    (heta : Tendsto eta atTop (𝓝 0))
    {K V : Set E} (hK : IsCompact K) (hV : IsCompact V) :
    TendstoUniformlyOn (fun n => coordinateGeodesicField (Q n).normalizedCoefficients)
      (coordinateGeodesicField g₀.metric.euclideanCoefficients) atTop (K ×ˢ V) := by
  have hzero : TendstoUniformlyOn (fun n => (Q n).normalizedCoefficients)
      g₀.metric.euclideanCoefficients atTop K := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn
        (tendstoUniformlyOn_initial_coefficient_jets g₀ S g tip scale eta Q heta 0 hK)
  have hone : TendstoUniformlyOn (fun n => fderiv ℝ (Q n).normalizedCoefficients)
      (fderiv ℝ g₀.metric.euclideanCoefficients) atTop K := by
    have he (B : E → Bilin) :
        (fun x => continuousMultilinearCurryFin1 ℝ E Bilin (iteratedFDeriv ℝ 1 B x)) =
          fderiv ℝ B := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simpa only [Function.comp_def, he] using
      (continuousMultilinearCurryFin1 ℝ E Bilin).isometry.uniformContinuous.comp_tendstoUniformlyOn
        (tendstoUniformlyOn_initial_coefficient_jets g₀ S g tip scale eta Q heta 1 hK)
  exact tendstoUniformlyOn_geodesicField_of_coefficients
    (contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients)
    g₀.metric.inner_isInvertible hK hV hzero hone



theorem tendstoUniformlyOn_initial_fderiv_geodesicFields
    (g₀ : StandardInitialMetric)
    (S : ℕ → GeneralizedSliceCarrier.{u})
    (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
    (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ)
    (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
    (heta : Tendsto eta atTop (𝓝 0))
    {K V : Set E} (hK : IsCompact K) (hV : IsCompact V) :
    TendstoUniformlyOn (fun n => fderiv ℝ (coordinateGeodesicField (Q n).normalizedCoefficients))
      (fderiv ℝ (coordinateGeodesicField g₀.metric.euclideanCoefficients)) atTop (K ×ˢ V) := by
  have hjet := tendstoUniformlyOn_initial_coefficient_jets g₀ S g tip scale eta Q heta
  have hzero : TendstoUniformlyOn (fun n => (Q n).normalizedCoefficients)
      g₀.metric.euclideanCoefficients atTop K := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn (hjet 0 hK)
  have hone := tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one (hjet 1 hK)
  have htwo := tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one
    (tendstoUniformlyOn_iteratedFDeriv_fderiv (hjet 2 hK))
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g₀ hK 0
  have hsmooth : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ ∞ (Q n).normalizedCoefficients x := by
    filter_upwards [heta.eventually (gt_mem_nhds hdelta)] with n hn
    intro x hx
    exact (Q n).contDiffOn_normalizedCoefficients.contDiffAt
      ((Q n).toPartialDiffeomorph.open_source.mem_nhds
        ((hdomain (eta n) (Q n).eta_pos hn.le).2 hx))
  exact tendstoUniformlyOn_fderiv_geodesicField_of_coefficients
    (contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients)
    g₀.metric.inner_isInvertible hK hV hsmooth hzero hone htwo

end ActualComparisons

end PoincareConjecture.M44
