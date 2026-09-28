import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessC0
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRoundFactor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60




theorem suRescaledRoundFactor_compact_bounds (a : LoopPlane) (t R : ℝ) :
    ∃ L N : ℝ, 0 ≤ L ∧ 0 ≤ N ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      let l := fun z : LoopPlane => suAlphaRoundFactor (s • (a + t • z))
      ∀ z ∈ Metric.closedBall 0 R, (l z)⁻¹ ≤ L ∧ ‖fderiv ℝ l z‖ ≤ N := by
  let K := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : LoopPlane) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  let A := fun q : ℝ × LoopPlane => q.1 • (a + t • q.2)
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hl : Continuous (fun q : ℝ × LoopPlane => (suAlphaRoundFactor (A q))⁻¹) :=
    (suRoundFactor_smooth_pos.1.continuous.comp hA).inv₀
      (fun q => (suRoundFactor_smooth_pos.2 (A q)).ne')
  have hd : Continuous (fun q : ℝ × LoopPlane =>
      (q.1 * t) • fderiv ℝ suAlphaRoundFactor (A q)) :=
    (continuous_fst.mul continuous_const).smul
      ((suRoundFactor_smooth_pos.1.continuous_fderiv (by simp)).comp hA)
  obtain ⟨L0, hL0⟩ := hK.exists_bound_of_continuousOn hl.continuousOn
  obtain ⟨N0, hN0⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  refine ⟨max L0 0, max N0 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro s hs l z hz
  constructor
  · have h := hL0 (s, z) ⟨hs, hz⟩
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (suRoundFactor_smooth_pos.2 _).le)] at h
    exact h.trans (le_max_left _ _)
  · have heq : l = fun y => suAlphaRoundFactor (s • a + (s * t) • y) := by
      funext y
      simp only [l, smul_add, smul_smul]
    rw [heq, suRescale_fderiv]
    have h := hN0 (s, z) ⟨hs, hz⟩
    simpa only [A, smul_add, smul_smul] using h.trans (le_max_left _ _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

open CoordinateExponential ConnectionVariation




theorem suChartReader_energy
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (z : LoopPlane)
    (hz : f z ∈ (extChartAt (𝓡 n) p).source)
    (hread : (fun q => L (e q)) =ᶠ[𝓝 (f z)] extChartAt (𝓡 n) p) :
    let u := fun y => L (e (f y))
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
    2 * m60EnergyDensity g f z =
      ∑ i : Fin 2, G (u z) (fderiv ℝ u z (b i)) (fderiv ℝ u z (b i)) := by
  intro u G
  have hg : u =ᶠ[𝓝 z] extChartAt (𝓡 n) p ∘ f :=
    hread.comp_tendsto hf.continuous.continuousAt
  rw [m60EnergyDensity_eq_chart g p (hf.mdifferentiable (by simp) z) hz,
    hg.fderiv_eq, hg.self_of_nhds]
  dsimp only [G, Function.comp_apply]
  ring




theorem suChartReader_weightedEuler
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (lambda : LoopPlane → ℝ) (rho c : ℝ) (z : LoopPlane)
    (hz : f z ∈ (extChartAt (𝓡 n) p).source)
    (hread : (fun q => L (e q)) =ᶠ[𝓝 (f z)] extChartAt (𝓡 n) p)
    (heq : let u := extChartAt (𝓡 n) p ∘ f
      let Gamma := christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      ∑ i : Fin 2, covDerivAlong Gamma u
        (fun y => (rho ^ 2 + 2 * m60EnergyDensity g f y / lambda y) ^ c •
          fderiv ℝ u y (b i)) (b i) z = 0) :
    let u := fun y => L (e (f y))
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
    let Gamma := christoffelBilinear G
    let Q := fun y => ∑ i : Fin 2, G (u y) (fderiv ℝ u y (b i)) (fderiv ℝ u y (b i))
    ∑ i : Fin 2, covDerivAlong Gamma u
      (fun y => (rho ^ 2 + Q y / lambda y) ^ c • fderiv ℝ u y (b i)) (b i) z = 0 := by
  intro u G Gamma Q
  let v := extChartAt (𝓡 n) p ∘ f
  have hg : u =ᶠ[𝓝 z] v := hread.comp_tendsto hf.continuous.continuousAt
  have hsource : ∀ᶠ y in 𝓝 z, f y ∈ (extChartAt (𝓡 n) p).source :=
    hf.continuous.continuousAt ((isOpen_extChartAt_source p).mem_nhds hz)
  have hQ : Q =ᶠ[𝓝 z] fun y => 2 * m60EnergyDensity g f y := by
    filter_upwards [hg.eventually_nhds, hsource] with y hy hys
    change u =ᶠ[𝓝 y] v at hy
    rw [m60EnergyDensity_eq_chart g p (hf.mdifferentiable (by simp) y) hys]
    dsimp only [Q]
    rw [hy.self_of_nhds, hy.fderiv_eq]
    dsimp only [v, G, Function.comp_apply]
    ring
  have hfield (i : Fin 2) :
      (fun y => (rho ^ 2 + Q y / lambda y) ^ c • fderiv ℝ u y (b i)) =ᶠ[𝓝 z]
      (fun y => (rho ^ 2 + 2 * m60EnergyDensity g f y / lambda y) ^ c •
        fderiv ℝ v y (b i)) := by
    filter_upwards [hQ, hg.fderiv (𝕜 := ℝ)] with y hy hyd
    rw [hy, hyd]
  calc
    _ = ∑ i : Fin 2, covDerivAlong Gamma v
        (fun y => (rho ^ 2 + 2 * m60EnergyDensity g f y / lambda y) ^ c •
          fderiv ℝ v y (b i)) (b i) z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [covDerivAlong_congr_base Gamma _ hg, covDerivAlong_congr Gamma v (hfield i)]
    _ = 0 := heq

end PoincareConjecture.M60
