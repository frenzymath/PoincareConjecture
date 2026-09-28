import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitHarmonic



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ





theorem suWeakPlaneCoordinates_smooth_harmonic
    (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g)
    (equation : ∀ (p : M) (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
      (center : LoopPlane) (radius : ℝ),
      SUWeakAlphaCoordinate g p 1 u V center radius → ContDiffAt ℝ ∞ u center →
      ∑ i : Fin 2, covDerivAlong
        (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)) u
        (fun y => fderiv ℝ u y (b i)) (b i) center = 0)
    {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d)) (f : C(LoopPlane, M))
    (hweak : ∀ a : LoopPlane,
      ∃ (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E) (R : ℝ), 0 < R ∧
        (∀ z ∈ Metric.closedBall a R, f z ∈ (extChartAt (𝓡 n) p).source ∧
          (fun q => L (e q)) =ᶠ[𝓝 (f z)] extChartAt (𝓡 n) p) ∧
        let u := fun z => L (e (f z))
        SUWeakAlphaCoordinate g p 1 u (fun i z => fderiv ℝ u z (b i)) a R) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧ SUPlaneHarmonic g f := by
  have hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f := by
    intro a
    obtain ⟨p, L, R, hR, hchart, S⟩ := hweak a
    let u := fun z => L (e (f z))
    have hc := hchart a (Metric.mem_closedBall_self hR.le)
    have hu : ContDiffAt ℝ ∞ u a := regular p u _ a R S
    have hvalue : u a = (extChartAt (𝓡 n) p) (f a) := hc.2.self_of_nhds
    have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) p).symm (u a) := by
      rw [hvalue]
      exact (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds ((extChartAt (𝓡 n) p).map_source hc.1))
    apply (hi.comp a (contMDiffAt_iff_contDiffAt.mpr hu)).congr_of_eventuallyEq
    filter_upwards [hc.2.comp_tendsto f.continuous.continuousAt,
      f.continuous.continuousAt ((isOpen_extChartAt_source p).mem_nhds hc.1)] with z hz hzs
    change L (e (f z)) = (extChartAt (𝓡 n) p) (f z) at hz
    change f z = (extChartAt (𝓡 n) p).symm (u z)
    rw [show u z = (extChartAt (𝓡 n) p) (f z) from hz,
      (extChartAt (𝓡 n) p).left_inv hzs]
  refine ⟨hf, ?_⟩
  intro q a hq
  obtain ⟨p, L, R, hR, hchart, S⟩ := hweak a
  let u := fun z => L (e (f z))
  have hc := hchart a (Metric.mem_closedBall_self hR.le)
  have hu : ContDiffAt ℝ ∞ u a := regular p u _ a R S
  have he := equation p u _ a R S hu
  have hg : u =ᶠ[𝓝 a] extChartAt (𝓡 n) p ∘ f :=
    hc.2.comp_tendsto f.continuous.continuousAt
  have hcol (i : Fin 2) : (fun y => fderiv ℝ u y (b i)) =ᶠ[𝓝 a]
      (fun y => fderiv ℝ (extChartAt (𝓡 n) p ∘ f) y (b i)) := by
    filter_upwards [hg.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  apply suHarmonic_change_target g f hf p q a hc.1 hq
  change (∑ i : Fin 2, covDerivAlong
    (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm))
    (extChartAt (𝓡 n) p ∘ f)
    (fun y => fderiv ℝ (extChartAt (𝓡 n) p ∘ f) y (b i)) (b i) a) = 0
  have hterm (i : Fin 2) := covDerivAlong_congr_base
    (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm))
    (fun y => fderiv ℝ u y (b i)) hg (b i)
  simp_rw [hterm, covDerivAlong_congr _ _ (hcol _)] at he
  exact he

end PoincareConjecture.M60
