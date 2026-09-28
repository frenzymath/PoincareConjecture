import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMetricIntegral
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusEnergyDensity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.WeightedAreaEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

private theorem m64_modulus_density_eq_area_of_conformal
    (g : RiemannianMetric n M) (f : LoopPlane → M) {r : ℝ} (hr : 0 < r)
    (z : LoopPlane)
    (hscale : r * m60AreaGram g f z 0 0 =
      r⁻¹ * m60AreaGram g f z 1 1)
    (horth : m60AreaGram g f z 0 1 = 0) :
    m64ModulusEnergyDensity g r f z = m60AreaDensity g f z := by
  let a0 := m60AreaGram g f z 0 0
  let b0 := m60AreaGram g f z 1 1
  have ha : 0 ≤ a0 := m60AreaGram_diagonal_nonneg g f z 0
  have hb : 0 ≤ b0 := m60AreaGram_diagonal_nonneg g f z 1
  have hrne : r ≠ 0 := ne_of_gt hr
  have hscale' : b0 = r ^ 2 * a0 := by
    calc
      b0 = (r * r⁻¹) * b0 := by rw [mul_inv_cancel₀ hrne, one_mul]
      _ = r * (r⁻¹ * b0) := by ring
      _ = r * (r * a0) := by rw [← hscale]
      _ = r ^ 2 * a0 := by ring
  have hdet : Matrix.det (m60AreaGram g f z) = (r * a0) ^ 2 := by
    rw [Matrix.det_fin_two, m60AreaGram_symm g f z 1 0, horth]
    simp only [zero_mul, sub_zero]
    change a0 * b0 = (r * a0) ^ 2
    rw [hscale']
    ring
  have hnonneg : 0 ≤ r * a0 := mul_nonneg hr.le ha
  have harea : m60AreaDensity g f z = r * a0 := by
    unfold m60AreaDensity
    rw [hdet, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hnonneg]
  unfold m64ModulusEnergyDensity
  rw [harea]
  rw [← hscale]
  ring

private theorem m64MixedModulusEnergy_contDiffAt
    (F : RicciFlow n M (Icc a b)) (r : ℝ) {v : ℝ × LoopPlane → M}
    {q : ℝ × (ℝ × LoopPlane)} (ht : q.1 ∈ Ioo a b)
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v q.2) :
    ContDiffAt ℝ ∞ (fun w : ℝ × (ℝ × LoopPlane) =>
      m64ModulusEnergyDensity (F.metric w.1) r
        (fun z => v (w.2.1, z)) w.2.2) q := by
  let u (i : Fin 2) (w : ℝ × LoopPlane) :=
    mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v w
      (0, EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hpush (i : Fin 2) :
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) ((𝓡 n).prod (𝓡 n)) ∞
        (fun w => (⟨v w, u i w⟩ : TangentBundle (𝓡 n) M)) q.2 := by
    have hd : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane)
        ((𝓘(ℝ, ℝ × LoopPlane)).prod 𝓘(ℝ, ℝ × LoopPlane)) ∞
        (fun w : ℝ × LoopPlane =>
          (⟨w, (0, EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
            TangentBundle 𝓘(ℝ, ℝ × LoopPlane) (ℝ × LoopPlane))) q.2 := by
      rw [contMDiffAt_totalSpace]
      refine ⟨contMDiffAt_id, ?_⟩
      simpa using contMDiffAt_const
        (c := ((0 : ℝ), EuclideanSpace.basisFun (Fin 2) ℝ i))
    exact (hv.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hd hv
  have hdomain : Icc a b ×ˢ (univ : Set M) ∈ 𝓝 (q.1, v q.2) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem
  have hmetric := (F.smooth.contMDiffAt hdomain).comp q
    (contDiffAt_fst.contMDiffAt.prodMk (hv.comp q contDiffAt_snd.contMDiffAt))
  have hscalar (i : Fin 2) : ContDiffAt ℝ ∞
      (fun w : ℝ × (ℝ × LoopPlane) =>
        (F.metric w.1).inner (v w.2) (u i w.2) (u i w.2)) q := by
    have h := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
      ((hpush i).comp q contDiffAt_snd.contMDiffAt)
      ((hpush i).comp q contDiffAt_snd.contMDiffAt)
    exact contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp h).2
  have hraw := ((contDiffAt_const (c := r)).mul (hscalar 0)).add
    ((contDiffAt_const (c := r⁻¹)).mul (hscalar 1))
  have hraw := hraw.div_const 2
  apply hraw.congr_of_eventuallyEq
  have hnear : ∀ᶠ w in 𝓝 q.2,
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) 1 v w :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hv.of_le (by simp))
  filter_upwards [(continuous_snd.tendsto q).eventually hnear] with w hw
  have hmd := hw.mdifferentiableAt one_ne_zero
  simp only [m64ModulusEnergyDensity, m60AreaGram,
    m64MovingAnnulus_spatial_differential hmd, u]





theorem m64ModulusAnnulusEnergy_hasDerivAt_of_local_moving_metric
    (F : RicciFlow n M (Icc a b)) (r : ℝ) {t : ℝ} (ht : t ∈ Ioo a b)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U)) :
    let E := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (F.metric (t + q.1)) r
        (fun z => v (q.1, z)) q.2
    IntegrableOn (fun p => fderiv ℝ E (0, p) (1, 0)) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
        (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 := by
  dsimp only
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (F.metric (t + q.1)) r
      (fun z => v (q.1, z)) q.2
  let delta := min epsilon (min (t - a) (b - t))
  have hdelta : 0 < delta := lt_min hepsilon
    (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  have hsmall : Ioo (-delta) delta ⊆ Ioo (-epsilon) epsilon :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have htime {s : ℝ} (hs : s ∈ Ioo (-delta) delta) :
      t + s ∈ Ioo a b := by
    have ha : delta ≤ t - a := (min_le_right _ _).trans (min_le_left _ _)
    have hb : delta ≤ b - t := (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith [hs.1, hs.2]
  have hopen : IsOpen (Ioo (-delta) delta ×ˢ U) := isOpen_Ioo.prod hU
  have hE : ContDiffOn ℝ ∞ E (Ioo (-delta) delta ×ˢ U) := by
    intro q hq
    have hmix := m64MixedModulusEnergy_contDiffAt F r (q := (t + q.1, q))
      (htime hq.1) (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
        ⟨hsmall hq.1, hq.2⟩))
    exact (hmix.comp (f := fun w : ℝ × LoopPlane => (t + w.1, w)) q
      (((contDiffAt_const (c := t)).add contDiffAt_fst).prodMk contDiffAt_id)).contDiffWithinAt
  have hF : ∀ s ∈ Ioo (-delta) delta,
      ContinuousOn (fun p => E (s, p)) m64AnnulusDomain := by
    intro s hs
    exact hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hs, hdom hp⟩)
  have hF' : ContinuousOn
      (Function.uncurry (fun s p => fderiv ℝ E (s, p) (1, 0)))
        (Ioo (-delta) delta ×ˢ m64AnnulusDomain) := by
    have hd := ((hE.fderiv_of_isOpen hopen (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := (1, (0 : LoopPlane))))).continuousOn
    exact hd.mono (prod_mono_right hdom)
  have hdiff : ∀ s ∈ Ioo (-delta) delta, ∀ p ∈ m64AnnulusDomain,
      HasDerivAt (fun z => E (z, p)) (fderiv ℝ E (s, p) (1, 0)) s := by
    intro s hs p hp
    exact ((hE.contDiffAt (hopen.mem_nhds ⟨hs, hdom hp⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (l := E) (f := fun z : ℝ => (z, p)) s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s p))
  have hresult := m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    (F := fun s p => E (s, p)) (F' := fun s p => fderiv ℝ E (s, p) (1, 0))
    hdelta hF hF' hdiff
  simpa only [E] using hresult







theorem m64AnnulusArea_forward_majorant_of_modulus_conformal_moving_metric
    (F : RicciFlow n M (Icc a b)) (r : ℝ) {t : ℝ} (ht : t ∈ Ioo a b)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U)) (hr : 0 < r)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) (fun z => v (0, z)) p 0 0 =
          r⁻¹ * m60AreaGram (F.metric t) (fun z => v (0, z)) p 1 1 ∧
        m60AreaGram (F.metric t) (fun z => v (0, z)) p 0 1 = 0) :
    let E := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (F.metric (t + q.1)) r
        (fun z => v (q.1, z)) q.2
    let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) ≤
        m64AnnulusArea (F.metric t) (fun p => v (0, p)) + h * (d + eta) := by
  dsimp only
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (F.metric (t + q.1)) r
      (fun z => v (q.1, z)) q.2
  let energy := fun s => ∫ p in m64AnnulusDomain, E (s, p)
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hcenter : m64AnnulusArea (F.metric t) (fun p => v (0, p)) = energy 0 := by
    apply integral_congr_ae
    filter_upwards [hconformal] with p hp
    simpa only [E, energy, add_zero] using (m64_modulus_density_eq_area_of_conformal (F.metric t)
      (fun p => v (0, p)) hr p hp.1 hp.2).symm
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (fun p => E (s, p)) m64AnnulusDomain volume := by
    have hslice : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (fun p => v (s, p)) U := by
      intro p hp
      have hline : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane) ∞
          (fun q : LoopPlane => (s, q)) p :=
        contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_id)
      simpa only [Function.comp_def] using
        ((hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hs, hp⟩)).comp p
          hline).contMDiffWithinAt
    have hE : ContDiffOn ℝ ∞
        (fun p => m64ModulusEnergyDensity (F.metric (t + s)) r
          (fun z => v (s, z)) p) U := by
      intro p hp
      have hvprod : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n)
          ∞ (fun q : ℝ × LoopPlane => v (s, q.2)) (0, p) :=
        by
          simpa only [Function.comp_def] using
            (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hs, hp⟩)).comp (0, p)
              (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_snd))
      have hfamily := m64ModulusEnergyDensity_family_contDiffAt
        (F.metric (t + s)) r (p := (0, p)) hvprod
      simpa only [Function.comp_def] using
        (hfamily.comp (f := fun z : LoopPlane => (0, z)) p
          ((contDiffAt_const (c := (0 : ℝ))).prodMk contDiffAt_id)).contDiffWithinAt
    exact (hE.continuousOn.mono hdom).integrableOn_compact
      m64AnnulusDomain_isCompact
  have hderiv : HasDerivAt energy d 0 := by
    simpa only [energy, E, d] using
      (m64ModulusAnnulusEnergy_hasDerivAt_of_local_moving_metric F r ht hepsilon
        hU hdom hv).2
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using
      hderiv.tendsto_slope_zero_right
  intro eta heta
  have hev := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right d heta))
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  filter_upwards [hev, htime, self_mem_nhdsWithin] with h hh hhs hpos
  have hupper : m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) ≤ energy h := by
    change (∫ p in m64AnnulusDomain,
      m60AreaDensity (F.metric (t + h)) (fun p => v (h, p)) p) ≤ energy h
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun p => m60AreaDensity_nonneg _ _ _)
      (hint h hhs)
      (Eventually.of_forall fun p => m60AreaDensity_le_weightedGram
        (F.metric (t + h)) (fun p => v (h, p)) p hr)
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter]
  exact hupper.trans (by linarith)

end PoincareConjecture
