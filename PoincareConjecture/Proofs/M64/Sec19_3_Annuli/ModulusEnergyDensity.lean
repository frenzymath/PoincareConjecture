import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusDensityCongruence
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




noncomputable def m64ModulusEnergyDensity (g : RiemannianMetric n M) (r : ℝ)
    (f : LoopPlane → M) (p : LoopPlane) : ℝ :=
  (r * m60AreaGram g f p 0 0 + r⁻¹ * m60AreaGram g f p 1 1) / 2





theorem m64ModulusEnergyDensity_congr_of_eventuallyEq
    (g : RiemannianMetric n M) (r : ℝ) {f h : LoopPlane → M} {p : LoopPlane}
    (heq : f =ᶠ[𝓝 p] h) : m64ModulusEnergyDensity g r f p = m64ModulusEnergyDensity g r h p := by
  have hi (v w : EuclideanSpace ℝ (Fin n)) : g.inner (f p) v w = g.inner (h p) v w :=
    congrArg (fun q : M => g.inner q v w) heq.eq_of_nhds
  simp only [m64ModulusEnergyDensity, m60AreaGram, heq.mfderiv_eq, hi]
  rfl





theorem m64ModulusEnergyDensity_ae_eq_of_eqOn
    (g : RiemannianMetric n M) (r : ℝ) {f h : LoopPlane → M}
    (heq : EqOn f h m64AnnulusDomain) :
    m64ModulusEnergyDensity g r f =ᵐ[volume.restrict m64AnnulusDomain]
      m64ModulusEnergyDensity g r h := by
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  apply m64ModulusEnergyDensity_congr_of_eventuallyEq g r
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  exact heq (interior_subset hq)





theorem m64AreaGram_eq_chart (g : RiemannianMetric n M) (b : M)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    (hp : f p ∈ (extChartAt (𝓡 n) b).source) (i j : Fin 2) :
    m60AreaGram g f p i j =
      g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (extChartAt (𝓡 n) b (f p))
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) (f p) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hp)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp p hc hf
  rw [mfderiv_eq_fderiv] at hd
  rw [hd]
  exact (ConjugateVariation.chartCoefficients_apply g b hp _ _).symm





theorem m64AreaGram_family_eq_chart (g : RiemannianMetric n M) (b : M)
    {v : ℝ × LoopPlane → M} {p : ℝ × LoopPlane}
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v p)
    (hp : v p ∈ (extChartAt (𝓡 n) b).source) (i j : Fin 2) :
    m60AreaGram g (fun z => v (p.1, z)) p.2 i j =
      g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (extChartAt (𝓡 n) b (v p))
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ v) p (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ v) p (0, EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane) (fun z => (p.1, z)) p.2 :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).differentiableAt.mdifferentiableAt
  have hslice : MDifferentiableAt (𝓡 2) (𝓡 n) (fun z => v (p.1, z)) p.2 :=
    hv.comp p.2 hi
  rw [m64AreaGram_eq_chart g b hslice hp]
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) (v p) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hp)).mdifferentiableAt (by simp)
  have hu : DifferentiableAt ℝ ((extChartAt (𝓡 n) b) ∘ v) p :=
    (hc.comp p hv).differentiableAt
  have hd : HasFDerivAt (fun z => extChartAt (𝓡 n) b (v (p.1, z)))
      ((fderiv ℝ ((extChartAt (𝓡 n) b) ∘ v) p).comp
        (ContinuousLinearMap.inr ℝ ℝ LoopPlane)) p.2 :=
    HasFDerivAt.comp p.2 (f := fun z : LoopPlane => (p.1, z))
      (g := (extChartAt (𝓡 n) b) ∘ v) hu.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  dsimp only [Function.comp_def] at hd ⊢
  rw [hd.fderiv]
  rfl





theorem m64AreaGram_family_contDiffAt (g : RiemannianMetric n M)
    {v : ℝ × LoopPlane → M} {p : ℝ × LoopPlane}
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v p) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => m60AreaGram g (fun z => v (q.1, z)) q.2 i j) p := by
  let b := v p
  let c := extChartAt (𝓡 n) b
  let u := c ∘ v
  let B := g.pullbackCoefficients c.symm
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (v p) := contMDiffAt_extChartAt
  have hu : ContDiffAt ℝ ∞ u p := contMDiffAt_iff_contDiffAt.mp (hc.comp p hv)
  have hB : ContDiffAt ℝ ∞ B (u p) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source (mem_extChartAt_source b)))
  have hdu (k : Fin 2) : ContDiffAt ℝ ∞
      (fun q => fderiv ℝ u q (0, EuclideanSpace.basisFun (Fin 2) ℝ k)) p :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hformula := ((hB.comp p hu).clm_apply (hdu i)).clm_apply (hdu j)
  apply hformula.congr_of_eventuallyEq
  have hchart : ∀ᶠ q in 𝓝 p, v q ∈ c.source :=
    hv.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds (mem_extChartAt_source b))
  have hnear : ∀ᶠ q in 𝓝 p, ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) 1 v q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hv.of_le (by simp))
  filter_upwards [hchart, hnear] with q hq hvq
  exact m64AreaGram_family_eq_chart g b (hvq.mdifferentiableAt one_ne_zero) hq i j





theorem m64ModulusEnergyDensity_family_contDiffAt (g : RiemannianMetric n M) (r : ℝ)
    {v : ℝ × LoopPlane → M} {p : ℝ × LoopPlane}
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v p) :
    ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity g r (fun z => v (q.1, z)) q.2) p := by
  exact ((contDiffAt_const.mul (m64AreaGram_family_contDiffAt g hv 0 0)).add
    (contDiffAt_const.mul (m64AreaGram_family_contDiffAt g hv 1 1))).div_const 2

end PoincareConjecture
