import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarAnnularEnergy









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem energy_contraction_of_angular_comparison
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {C0 : ℝ} (hC0 : 0 < C0)
    (hcomp : ∀ (a : LoopPlane) (rho : ℝ), 0 < rho → closedBall a rho ⊆ S →
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        A.diskEnergy B a (rho * Real.exp (-s)) ≤ C0 * A.angularEnergy a rho s) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      closedBall a rho ⊆ S →
      A.diskEnergy B a (rho * Real.exp (-1)) ≤ q * A.diskEnergy B a rho := by
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  refine ⟨(L + 1) / (L + 2), div_pos (by linarith) hL2,
    (div_lt_one hL2).mpr (by linarith), ?_⟩
  intro a rho hrho hKS
  let Y := A.diskEnergy B a (rho * Real.exp (-1))
  let X := A.diskEnergy B a rho
  have hball : ball a rho ⊆ S := ball_subset_closedBall.trans hKS
  have hYX : Y ≤ X := A.diskEnergy_mono B hB hei hb hpos a
    (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), Y ≤ C0 * A.angularEnergy a rho s := by
    filter_upwards [hcomp a rho hrho hKS, ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
    have hlarge : rho * Real.exp (-s) ≤ rho :=
      mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
    exact (A.diskEnergy_mono B hB hei hb hpos a hsmall
      ((ball_subset_ball hlarge).trans hball)).trans hs
  have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1, A.angularEnergy a rho s := by
    have hh := integral_mono_ae (integrable_const Y)
      ((A.angularEnergy_integrable a hrho hKS).const_mul C0) hpoint
    rw [integral_const_mul] at hh
    simpa using hh
  have hshell := A.angularEnergy_integral_le_annular_energy B hB hei hb hpos hC hcoercive
    a hrho hKS
  have hY : Y ≤ L * (X - Y) := hYint.trans
    ((mul_le_mul_of_nonneg_left hshell hC0.le).trans_eq (by dsimp only [L, X, Y]; ring))
  change Y ≤ (L + 1) / (L + 2) * X
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL2).mpr
  nlinarith

end PoincareConjecture.M64ObservedWeakAnnulus
