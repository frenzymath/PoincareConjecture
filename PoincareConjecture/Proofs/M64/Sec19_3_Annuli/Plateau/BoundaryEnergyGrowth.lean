import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryAngularShellEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthPower
import PoincareConjecture.Proofs.M64.Mathlib.LogRadiusAE

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

theorem boundary_uniform_energy_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {I : Set ℝ} {width C0 : ℝ} (hw : 0 < width) (hC0 : 0 < C0)
    (hwindow : ∀ x ∈ I, width < x ∧ x + width < curvePeriod) (hw1 : width < 1)
    (hcomp : ∀ x ∈ I, ∀ epsilon R : ℝ, 0 < epsilon → R ≤ width →
      ∀ᵐ r ∂volume.restrict (Icc epsilon R),
        A.boundaryDiskEnergy B x r ≤ C0 * A.boundaryAngularEnergy x r) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ I, ∀ r ∈ Ioc (0 : ℝ) width,
        A.boundaryDiskEnergy B x r ≤ K * r ^ beta := by
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  let q := (L + 1) / (L + 2)
  have hq : 0 < q := div_pos (by linarith) hL2
  have hq1 : q < 1 := (div_lt_one hL2).mpr (by linarith)
  have hstep (x : ℝ) (hx : x ∈ I) (rho : ℝ) (hrho : rho ∈ Ioc (0 : ℝ) width) :
      A.boundaryDiskEnergy B x (rho * Real.exp (-1)) ≤ q * A.boundaryDiskEnergy B x rho := by
    let Y := A.boundaryDiskEnergy B x (rho * Real.exp (-1))
    let X := A.boundaryDiskEnergy B x rho
    have hmono := A.boundaryDiskEnergy_mono B hB hei hb hpos x
    have hYX : Y ≤ X := hmono (mul_le_of_le_one_right hrho.1.le
      (Real.exp_le_one_iff.mpr (by norm_num)))
    have hgood := m64LogRadius_ae hrho.1
      (hcomp x hx (rho * Real.exp (-1)) rho (mul_pos hrho.1 (Real.exp_pos _)) hrho.2)
    have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        Y ≤ C0 * A.boundaryAngularEnergy x (rho * Real.exp (-s)) := by
      filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with s hs hsI
      have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.1.le
      exact (hmono hsmall).trans hs
    obtain ⟨hi, hshell⟩ := A.boundaryAngularEnergy_shell_bound B hB hei hb hpos hC
      hcoercive hrho.1 (hrho.2.trans_lt (hwindow x hx).1)
      (by linarith [(hwindow x hx).2, hrho.2]) (hrho.2.trans_lt hw1)
    have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1,
        A.boundaryAngularEnergy x (rho * Real.exp (-s)) := by
      have hh := integral_mono_ae (integrable_const Y) (hi.const_mul C0) hpoint
      rw [integral_const_mul] at hh
      simpa using hh
    have hY : Y ≤ L * (X - Y) := hYint.trans
      ((mul_le_mul_of_nonneg_left hshell hC0.le).trans_eq (by dsimp only [L, X, Y]; ring))
    change Y ≤ (L + 1) / (L + 2) * X
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hL2).mpr
    nlinarith
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := m64Morrey_exists_uniform_power_of_contraction
    hw hq hq1 (A.energy_nonneg B hpos)
  refine ⟨beta, hbeta, K, hK, ?_⟩
  intro x hx r hr
  exact hpower (A.boundaryDiskEnergy B x)
    ((A.boundaryDiskEnergy_mono B hB hei hb hpos x).monotoneOn _)
    (A.boundaryDiskEnergy_le_energy B hB hei hb hpos x width) (hstep x hx) r hr

theorem boundary_uniform_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {I : Set ℝ} {width C0 : ℝ} (hw : 0 < width) (hC0 : 0 < C0)
    (hwindow : ∀ x ∈ I, width < x ∧ x + width < curvePeriod) (hw1 : width < 1)
    (hcomp : ∀ x ∈ I, ∀ epsilon R : ℝ, 0 < epsilon → R ≤ width →
      ∀ᵐ r ∂volume.restrict (Icc epsilon R),
        A.boundaryDiskEnergy B x r ≤ C0 * A.boundaryAngularEnergy x r) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ I, ∀ r ∈ Ioc (0 : ℝ) width, ∀ i : Fin 2,
        (∫ p in closedBall (annulusPoint x 0) r ∩ S, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := A.boundary_uniform_energy_power_growth B hB hei hb
    hpos hC hcoercive hw hC0 hwindow hw1 hcomp
  refine ⟨beta, hbeta, 2 * C * K, by positivity, ?_⟩
  intro x hx r hr i
  calc
    _ ≤ 2 * C * A.boundaryDiskEnergy B x r :=
      A.column_boundaryDisk_energy_le B hB hei hb hpos hC hcoercive x r i
    _ ≤ 2 * C * (K * r ^ beta) :=
      mul_le_mul_of_nonneg_left (hpower x hx r hr) (by positivity)
    _ = _ := by ring

end PoincareConjecture.M64ObservedWeakAnnulus
