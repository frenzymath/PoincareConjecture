import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CircleConeComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarAnnularEnergy

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem M64ObservedWeakAnnulus.energy_contraction
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ W.energy Q) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      Metric.closedBall a rho ⊆ S →
      A.diskEnergy Q a (rho * Real.exp (-1)) ≤ q * A.diskEnergy Q a rho := by
  obtain ⟨C0, hC0, hcomp⟩ := A.circle_energy_comparison g he hei hread Q hQ hpos hmin
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  refine ⟨(L + 1) / (L + 2), div_pos (by linarith) hL2,
    (div_lt_one hL2).mpr (by linarith), ?_⟩
  intro a rho hrho hKS
  let Y := A.diskEnergy Q a (rho * Real.exp (-1))
  let X := A.diskEnergy Q a rho
  have hball : Metric.ball a rho ⊆ S := Metric.ball_subset_closedBall.trans hKS
  have hYX : Y ≤ X := A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos a
    (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
  have hYpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      Y ≤ C0 * A.angularEnergy a rho s := by
    filter_upwards [hcomp a rho hrho hKS, ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
    have hlarge : rho * Real.exp (-s) ≤ rho :=
      mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
    exact (A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos a hsmall
      ((Metric.ball_subset_ball hlarge).trans hball)).trans hs
  have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1, A.angularEnergy a rho s := by
    have hi := integral_mono_ae (integrable_const Y)
      ((A.angularEnergy_integrable a hrho hKS).const_mul C0) hYpoint
    rw [integral_const_mul] at hi
    simpa using hi
  have hangular := A.angularEnergy_integral_le_annular_energy
    Q hQ hei.isEmbedding hb hpos hC hcoercive a hrho hKS
  have hY : Y ≤ L * (X - Y) :=
    hYint.trans ((mul_le_mul_of_nonneg_left hangular hC0.le).trans_eq (by dsimp [L, X, Y]; ring))
  change Y ≤ (L + 1) / (L + 2) * X
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL2).mpr
  nlinarith

end PoincareConjecture
