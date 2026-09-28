import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapChartVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64AnnulusEnergy_hasDerivAt_of_boundary_supported_variation
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {O K : Set LoopPlane} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∉ K, v (s, p) = v (0, p))
    (hint : ∀ s ∈ Ioo (-epsilon) epsilon,
      IntegrableOn (m60EnergyDensity g (fun p => v (s, p))) m64AnnulusDomain volume) :
    let D := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun p => v (q.1, p)) q.2 -
        m60EnergyDensity g (fun p => v (0, p)) q.2
    IntegrableOn (fun p => fderiv ℝ D (0, p) (1, 0)) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m60EnergyDensity g (fun z => v (s, z)) p)
        (∫ p in m64AnnulusDomain, fderiv ℝ D (0, p) (1, 0)) 0 := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
  let D := fun q : ℝ × LoopPlane => E q - E (0, q.2)
  let G := fun s p => fderiv ℝ D (s, p) (1, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hopen : IsOpen (Ioo (-epsilon) epsilon ×ˢ (univ : Set LoopPlane)) :=
    isOpen_Ioo.prod isOpen_univ
  have hDzero (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon)
      (p : LoopPlane) (hp : p ∉ K) : D (s, p) = 0 := by
    apply sub_eq_zero.mpr
    apply m60EnergyDensity_congr_of_eventuallyEq g
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hp] with z hz
    exact hfix s hs z hz
  have hD : ContDiffOn ℝ ∞ D (Ioo (-epsilon) epsilon ×ˢ univ) := by
    intro q hq
    by_cases hqO : q.2 ∈ O
    · have hEq : ContDiffAt ℝ ∞ E q := m60EnergyDensity_family_contDiffAt g
        (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hq.1, hqO⟩))
      have hEzero : ContDiffAt ℝ ∞ E (0, q.2) := m60EnergyDensity_family_contDiffAt g
        (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hzero, hqO⟩))
      exact (hEq.sub (hEzero.comp q
        (contDiffAt_const.prodMk contDiffAt_snd))).contDiffWithinAt
    · have hqK : q.2 ∉ K := fun h => hqO (hKO h)
      have hdq : ContDiffAt ℝ ∞ D q :=
        (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (by
          filter_upwards [(isOpen_Ioo.prod hK.isClosed.isOpen_compl).mem_nhds
            ⟨hq.1, hqK⟩] with p hp
          exact hDzero p.1 hp.1 p.2 hp.2)
      exact hdq.contDiffWithinAt
  have hDs (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      Continuous (fun p => D (s, p)) :=
    hD.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun p => ⟨hs, mem_univ p⟩)
  have hG : ContinuousOn (Function.uncurry G)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    ((hD.fderiv_of_isOpen hopen (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hder (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) (p : LoopPlane) :
      HasDerivAt (fun t => D (t, p)) (G s p) s := by
    have hDp : DifferentiableAt ℝ D (s, p) :=
      (hD.contDiffAt (hopen.mem_nhds ⟨hs, mem_univ p⟩)).differentiableAt (by simp)
    exact hDp.hasFDerivAt.comp_hasDerivAt (l := D) (f := fun s : ℝ => (s, p)) s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s p))
  obtain ⟨hGint, hderiv⟩ := m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    (F := fun s p => D (s, p)) (F' := G) hepsilon
    (fun s hs => (hDs s hs).continuousOn) (hG.mono (prod_mono_right (subset_univ _)))
    (fun s hs p _ => hder s hs p)
  refine ⟨hGint, ?_⟩
  apply (hderiv.add_const (∫ p in m64AnnulusDomain, E (0, p))).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  change (∫ p in m64AnnulusDomain, E (s, p)) =
    (∫ p in m64AnnulusDomain, E (s, p) - E (0, p)) +
      ∫ p in m64AnnulusDomain, E (0, p)
  rw [integral_sub (hint s hs) (hint 0 hzero)]
  ring

open CoordinateExponential ConnectionVariation ConjugateVariation

theorem m64AnnulusEnergy_hasDerivAt_of_boundary_supported_chart
    (g : RiemannianMetric n M) (b : M) (f : LoopPlane → M)
    {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O)
    (hfO : MapsTo f O (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ O,
      v (s, p) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, p)) = extChartAt (𝓡 n) b (f p) + s • V p)
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∉ tsupport V, v (s, p) = f p)
    (hint : ∀ s ∈ Ioo (-epsilon) epsilon,
      IntegrableOn (m60EnergyDensity g (fun p => v (s, p))) m64AnnulusDomain volume) :
    let u := (extChartAt (𝓡 n) b) ∘ f
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let D := fun p => ∑ i : Fin 2, B (u p)
      (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    IntegrableOn D m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m60EnergyDensity g (fun z => v (s, z)) p) (∫ p in m64AnnulusDomain, D p) 0 := by
  let u := (extChartAt (𝓡 n) b) ∘ f
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let D := fun p => ∑ i : Fin 2, B (u p)
    (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
    (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => v (q.1, z)) q.2
  let F := fun q : ℝ × LoopPlane => E q - E (0, q.2)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hfixed : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∉ tsupport V,
      v (s, p) = v (0, p) := by
    intro s hs p hp
    exact (hfix s hs p hp).trans (hfix 0 hzero p hp).symm
  obtain ⟨hFi, hFd⟩ := m64AnnulusEnergy_hasDerivAt_of_boundary_supported_variation
    g hepsilon hO hVc hVO hv hfixed hint
  have hpoint (p : LoopPlane) : fderiv ℝ F (0, p) (1, 0) = D p := by
    by_cases hp : p ∈ tsupport V
    · have hEp : ContDiffAt ℝ ∞ E (0, p) := m60EnergyDensity_family_contDiffAt g
        (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hzero, hVO hp⟩))
      have hzeroMap : ContDiffAt ℝ ∞
          (fun q : ℝ × LoopPlane => ((0 : ℝ), q.2)) (0, p) :=
        contDiffAt_const.prodMk contDiffAt_snd
      have hEzero : ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => E (0, q.2)) (0, p) :=
        hEp.comp (g := E) (f := fun q : ℝ × LoopPlane => ((0 : ℝ), q.2)) (0, p) hzeroMap
      have hFp : ContDiffAt ℝ ∞ F (0, p) := hEp.sub hEzero
      have hd : HasDerivAt (fun s => F (s, p)) (fderiv ℝ F (0, p) (1, 0)) 0 :=
        (hFp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
          (l := F) (f := fun s : ℝ => (s, p)) (0 : ℝ)
          ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) p))
      exact hd.unique ((m64EnergyDensity_hasDerivAt_of_affine_chart
        g b f hO hf hfO V hV hepsilon hv hcoord p (hVO hp)).sub_const (E (0, p)))
    · have hFeq : F =ᶠ[𝓝 (0, p)] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_Ioo.prod (isClosed_tsupport V).isOpen_compl).mem_nhds
          ⟨hzero, hp⟩] with q hq
        apply sub_eq_zero.mpr
        apply m60EnergyDensity_congr_of_eventuallyEq g
        filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hq.2] with z hz
        exact hfixed q.1 hq.1 z hz
      rw [hFeq.fderiv_eq]
      simp only [D, fderiv_const_apply, zero_apply, covDerivAlong_def,
        image_eq_zero_of_notMem_tsupport hp, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp,
        map_zero, add_zero, Finset.sum_const_zero]
  have hae : (fun p => fderiv ℝ F (0, p) (1, 0)) =ᵐ[volume.restrict m64AnnulusDomain] D :=
    Eventually.of_forall hpoint
  refine ⟨hFi.congr hae, ?_⟩
  have heq := integral_congr_ae hae
  change HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
    (∫ p in m64AnnulusDomain, fderiv ℝ F (0, p) (1, 0)) 0 at hFd
  rw [heq] at hFd
  exact hFd

end PoincareConjecture
