import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamCircleComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPolarEnergy







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusSeamDomain



theorem seam_energy_contraction
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      2 * rho < curvePeriod → Metric.closedBall a rho ⊆ O →
      A.seamDiskEnergy Q a (rho * Real.exp (-1)) ≤ q * A.seamDiskEnergy Q a rho := by
  obtain ⟨C0, hC0, hcomp⟩ := A.seam_circle_energy_comparison g he hei hread Q hQ hpos hmin
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  refine ⟨(L + 1) / (L + 2), div_pos (by linarith) hL2,
    (div_lt_one hL2).mpr (by linarith), ?_⟩
  intro a rho hrho hwidth hKO
  let Y := A.seamDiskEnergy Q a (rho * Real.exp (-1))
  let X := A.seamDiskEnergy Q a rho
  have hball : Metric.ball a rho ⊆ O := Metric.ball_subset_closedBall.trans hKO
  have hYX : Y ≤ X := A.seamDiskEnergy_mono Q hQ hei.isEmbedding hb hpos a
    (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
  have hYpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      Y ≤ C0 * A.seamAngularEnergy a rho s := by
    filter_upwards [hcomp a rho hrho hwidth hKO, ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
    have hlarge : rho * Real.exp (-s) ≤ rho :=
      mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
    exact (A.seamDiskEnergy_mono Q hQ hei.isEmbedding hb hpos a hsmall
      ((Metric.ball_subset_ball hlarge).trans hball)).trans hs
  have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1, A.seamAngularEnergy a rho s := by
    have hi := integral_mono_ae (integrable_const Y)
      ((A.seamAngularEnergy_integrable a hrho hKO).const_mul C0) hYpoint
    rw [integral_const_mul] at hi
    simpa using hi
  have hangular := A.seamAngularEnergy_integral_le_annular_energy
    Q hQ hei.isEmbedding hb hpos hC hcoercive a hrho hKO
  have hY : Y ≤ L * (X - Y) :=
    hYint.trans ((mul_le_mul_of_nonneg_left hangular hC0.le).trans_eq (by dsimp [L, X, Y]; ring))
  change Y ≤ (L + 1) / (L + 2) * X
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL2).mpr
  nlinarith

end PoincareConjecture.M64ObservedWeakAnnulus
