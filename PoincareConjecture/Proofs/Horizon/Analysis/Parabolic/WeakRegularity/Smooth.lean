import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.TimeSpatialRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.Sobolev
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.LocalEllipticity
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.SmoothRepresentative











noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

open Interior Sobolev.BoundaryCoordinates



theorem contDiffOn_of_continuous_weakSolution
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) : ContDiffOn ℝ ∞ u U := by
  have hV : IsOpen ((split n) ⁻¹' U) := hU.preimage (split n).continuous
  have huV : ContinuousOn (u ∘ split n) ((split n) ⁻¹' U) :=
    hu.comp (split n).continuous.continuousOn (fun _ hx => hx)
  obtain ⟨v, hv, hvu⟩ :=
    Sobolev.EuclideanIteratedEmbedding.exists_smooth_representative_of_memWkp_locally
      (u := u ∘ split n) (Ω := (split n) ⁻¹' U) (by
        intro x hx k
        obtain ⟨r, hr, hrU, hjet⟩ := exists_local_time_spatial_weak_jets
          (m := k) (k := k) hU hC hEll hu hw hx
        refine ⟨(split n) ⁻¹' Metric.ball (split n x) r,
          Metric.isOpen_ball.preimage (split n).continuous,
          Metric.mem_ball_self hr, ?_, ?_⟩
        · intro y hy
          exact hrU (Metric.ball_subset_closedBall hy)
        · exact (hjet.canonical Metric.isOpen_ball).memWkp_comp_split Metric.isOpen_ball)
  have heq := Measure.eqOn_open_of_ae_eq hvu hV hv.continuousOn huV
  have huc : ContDiffOn ℝ ∞ (u ∘ split n) ((split n) ⁻¹' U) :=
    hv.congr (fun x hx => (heq hx).symm)
  have hback := huc.comp (split n).symm.contDiff.contDiffOn
    (show MapsTo (split n).symm U ((split n) ⁻¹' U) from
      fun y hy => by simpa using hy)
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hback



theorem contDiffOn_of_continuous_weakSolution_positive
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hpos : ∀ z ∈ U, ∀ ξ : Euclid n, ξ ≠ 0 →
      0 < ∑ i, ∑ j, C.principal i j z * ξ i * ξ j)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) : ContDiffOn ℝ ∞ u U := by
  intro z hz
  obtain ⟨r, hr, hrU, κ, hκ, hEll⟩ :=
    exists_uniformlyElliptic_closedBall hU C hC hpos hz
  have hbU : Metric.ball z r ⊆ U := Metric.ball_subset_closedBall.trans hrU
  have hCb : C.IsSmoothOn (Metric.ball z r) :=
    ⟨fun i j => (hC.1 i j).mono hbU,
      fun i => (hC.2.1 i).mono hbU, hC.2.2.mono hbU⟩
  have hwb : WeakSolutionOn C u (Metric.ball z r) :=
    ⟨hw.1.mono_set hbU, fun φ hφ hφc hφb => hw.2 φ hφ hφc (hφb.trans hbU)⟩
  exact ((contDiffOn_of_continuous_weakSolution Metric.isOpen_ball hCb
    ⟨κ, hκ, fun x hx => hEll x (Metric.ball_subset_closedBall hx)⟩
    (hu.mono hbU) hwb).contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr))).contDiffWithinAt

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
