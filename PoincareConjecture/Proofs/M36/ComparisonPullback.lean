import PoincareConjecture.Proofs.M36.ComparisonChart
import PoincareConjecture.Proofs.M36.ComparisonSmoothJets
import PoincareConjecture.Proofs.M36.CenteredNeckMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section General

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]

theorem pullbackCoefficients_comp (g : RiemannianMetric 3 M)
    {f : E₃ → M} {k : E₃ → E₃} {p : E₃}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (k p)) (hk : ContDiffAt ℝ ∞ k p) :
    g.pullbackCoefficients (f ∘ k) p =
      ContinuousLinearMap.bilinearComp (g.pullbackCoefficients f (k p))
        (fderiv ℝ k p) (fderiv ℝ k p) := by
  have hcomp := mfderiv_comp p (hf.mdifferentiableAt (by simp))
    (hk.contMDiffAt.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hcomp
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (f (k p)) (mfderiv (𝓡 3) (𝓡 3) (f ∘ k) p v)
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ k) p w) = _
  rw [hcomp]
  rfl

theorem pullbackCoefficients_dilation (g : RiemannianMetric 3 M)
    {f : E₃ → M} (a : ℝ) (p : E₃)
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (a • p)) :
    g.pullbackCoefficients (fun x => f (a • x)) p =
      a ^ 2 • g.pullbackCoefficients f (a • p) := by
  have hd : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun x : E₃ => a • x) p :=
    (contDiff_id.const_smul a).contMDiff.contMDiffAt
  have hder : mfderiv (𝓡 3) (𝓡 3) (fun x : E₃ => a • x) p =
      a • ContinuousLinearMap.id ℝ E₃ := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id p).const_smul a).fderiv
  have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x => f (a • x)) p =
      (mfderiv (𝓡 3) (𝓡 3) f (a • p)).comp (a • ContinuousLinearMap.id ℝ E₃) := by
    rw [← hder]
    exact mfderiv_comp p (hf.mdifferentiableAt (by simp))
      (hd.mdifferentiableAt (by simp))
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (f (a • p))
    (mfderiv (𝓡 3) (𝓡 3) (fun x => f (a • x)) p v)
    (mfderiv (𝓡 3) (𝓡 3) (fun x => f (a • x)) p w) = _
  rw [hcomp]
  change g.inner (f (a • p))
    (mfderiv (𝓡 3) (𝓡 3) f (a • p) (a • v))
    (mfderiv (𝓡 3) (𝓡 3) f (a • p) (a • w)) =
      a ^ 2 * g.inner (f (a • p))
        (mfderiv (𝓡 3) (𝓡 3) f (a • p) v)
        (mfderiv (𝓡 3) (𝓡 3) f (a • p) w)
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem pullbackCoefficients_rescaled (g : RiemannianMetric 3 M)
    (lambda : ℝ) (hlambda : 0 < lambda) (f : E₃ → M) (p : E₃) :
    (m01RescaledMetric g lambda hlambda).pullbackCoefficients f p =
      lambda • g.pullbackCoefficients f p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact m01RescaledMetric_inner g lambda hlambda (f p)
    (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w)

end General

theorem dilatedSurgeryBallChart_pullbackCoefficients (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)]
    (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L))
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 R) :
    h.pullbackCoefficients (dilatedSurgeryBallChart g₀ L a) p =
      a ^ 2 • h.pullbackCoefficients (surgeryBallChart g₀ L) (a • p) := by
  apply pullbackCoefficients_dilation
  have hmem := dilation_mem_surgeryBall g₀ ha hR hfit hp
  exact (surgeryBallChart_contMDiffOn g₀ L _ hmem).contMDiffAt
    (Metric.isOpen_ball.mem_nhds hmem)

theorem dilatedSurgeryBallChart_error (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)]
    (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L)) (lambda : ℝ)
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 R) :
    lambda • h.pullbackCoefficients (dilatedSurgeryBallChart g₀ L a) p -
        g₀.metric.euclideanCoefficients p =
      a ^ 2 • (lambda • h.pullbackCoefficients (surgeryBallChart g₀ L) (a • p) -
        g₀.metric.euclideanCoefficients (a • p)) + standardDilationError g₀ a p := by
  rw [dilatedSurgeryBallChart_pullbackCoefficients g₀ ha hR hfit h hp]
  unfold standardDilationError
  module

end PoincareConjecture.M36
