import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.StereographicConformal










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60EnergyDensity_congr_of_eventuallyEq (g : RiemannianMetric n M)
    {f h : LoopPlane → M} {z : LoopPlane} (hf : f =ᶠ[𝓝 z] h) :
    m60EnergyDensity g f z = m60EnergyDensity g h z := by
  have hi (v w : EuclideanSpace ℝ (Fin n)) : g.inner (f z) v w = g.inner (h z) v w :=
    congrArg (fun p : M => g.inner p v w) hf.eq_of_nhds
  simp only [m60EnergyDensity, m60AreaGram, hf.mfderiv_eq, hi]
  rfl



theorem m60EnergyDensity_eq_chart (g : RiemannianMetric n M) (b : M)
    {φ : LoopPlane → M} {z : LoopPlane}
    (hφ : MDifferentiableAt (𝓡 2) (𝓡 n) φ z)
    (hz : φ z ∈ (extChartAt (𝓡 n) b).source) :
    m60EnergyDensity g φ z =
      (1 / 2 : ℝ) * ∑ i : Fin 2,
        g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (extChartAt (𝓡 n) b (φ z))
          (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) (φ z) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hz)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z hc hφ
  rw [mfderiv_eq_fderiv] at hd
  unfold m60EnergyDensity Matrix.trace m60AreaGram
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hd]
  exact (ConjugateVariation.chartCoefficients_apply g b hz _ _).symm



theorem m60EnergyDensity_family_eq_chart (g : RiemannianMetric n M) (b : M)
    {φ : ℝ × LoopPlane → M} {p : ℝ × LoopPlane}
    (hφ : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) φ p)
    (hp : φ p ∈ (extChartAt (𝓡 n) b).source) :
    m60EnergyDensity g (fun z => φ (p.1, z)) p.2 =
      (1 / 2 : ℝ) * ∑ i : Fin 2,
        g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (extChartAt (𝓡 n) b (φ p))
          (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ φ) p (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ φ) p (0, EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane) (fun z => (p.1, z)) p.2 :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).differentiableAt.mdifferentiableAt
  have hslice : MDifferentiableAt (𝓡 2) (𝓡 n) (fun z => φ (p.1, z)) p.2 := hφ.comp p.2 hi
  rw [m60EnergyDensity_eq_chart g b hslice hp]
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) (φ p) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hp)).mdifferentiableAt (by simp)
  have hu : DifferentiableAt ℝ ((extChartAt (𝓡 n) b) ∘ φ) p :=
    (hc.comp p hφ).differentiableAt
  have hd : HasFDerivAt (fun z => extChartAt (𝓡 n) b (φ (p.1, z)))
      ((fderiv ℝ ((extChartAt (𝓡 n) b) ∘ φ) p).comp
        (ContinuousLinearMap.inr ℝ ℝ LoopPlane)) p.2 :=
    HasFDerivAt.comp p.2 (f := fun z : LoopPlane => (p.1, z))
      (g := (extChartAt (𝓡 n) b) ∘ φ) hu.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  dsimp only [Function.comp_def] at hd ⊢
  rw [hd.fderiv]
  rfl



theorem m60EnergyDensity_family_contDiffAt (g : RiemannianMetric n M)
    {φ : ℝ × LoopPlane → M} {p : ℝ × LoopPlane}
    (hφ : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ φ p) :
    ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => φ (q.1, z)) q.2) p := by
  let b := φ p
  let c := extChartAt (𝓡 n) b
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ p) := contMDiffAt_extChartAt
  have hu : ContDiffAt ℝ ∞ u p := contMDiffAt_iff_contDiffAt.mp (hc.comp p hφ)
  have hB : ContDiffAt ℝ ∞ B (u p) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source (mem_extChartAt_source b)))
  have hdu (i : Fin 2) : ContDiffAt ℝ ∞
      (fun q => fderiv ℝ u q (0, EuclideanSpace.basisFun (Fin 2) ℝ i)) p :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hE : ContDiffAt ℝ ∞ (fun q => (1 / 2 : ℝ) * ∑ i : Fin 2,
      B (u q) (fderiv ℝ u q (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ u q (0, EuclideanSpace.basisFun (Fin 2) ℝ i))) p :=
    contDiffAt_const.mul (ContDiffAt.sum fun i _ =>
      (((hB.comp p hu).clm_apply (hdu i)).clm_apply (hdu i)))
  apply hE.congr_of_eventuallyEq
  have hchart : ∀ᶠ q in 𝓝 p, φ q ∈ c.source :=
    hφ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds (mem_extChartAt_source b))
  have hnear : ∀ᶠ q in 𝓝 p, ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) 1 φ q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hφ.of_le (by simp))
  filter_upwards [hchart, hnear]
    with q hq hφq
  exact m60EnergyDensity_family_eq_chart g b (hφq.mdifferentiableAt one_ne_zero) hq

end PoincareConjecture
