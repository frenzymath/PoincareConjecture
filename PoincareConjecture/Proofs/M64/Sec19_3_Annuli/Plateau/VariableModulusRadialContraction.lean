import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusRadialCircle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialPolarEnergy












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain



theorem weighted_lower_energy_contraction
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ (a : LoopPlane), a 1 = 0 → ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
        closedBall a rho ⊆ O → A.lowerDiskEnergy Q a (rho * Real.exp (-1)) ≤
          q * A.lowerDiskEnergy Q a rho + D * rho ^ 2 := by
  obtain ⟨rho0, hrho0, C0, hC0, hcomp⟩ :=
    A.weighted_lower_circle_energy_comparison g he hei hread hc0 hc0P Q hQ hpos hmodulus hmin
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  refine ⟨rho0, hrho0, (L + 1) / (L + 2), div_pos (by linarith) hL2,
    (div_lt_one hL2).mpr (by linarith), C0 / (L + 2), div_nonneg hC0.le hL2.le, ?_⟩
  intro a ha rho hrho hrrho0 hKO
  let Y := A.lowerDiskEnergy Q a (rho * Real.exp (-1))
  let X := A.lowerDiskEnergy Q a rho
  have hball : ball a rho ⊆ O := ball_subset_closedBall.trans hKO
  have hYX : Y ≤ X := A.lowerDiskEnergy_mono hce Q hQ hei.isEmbedding hb hpos a
    (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
  have hYpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      Y ≤ C0 * (A.lowerAngularEnergy a rho s + rho ^ 2) := by
    filter_upwards [hcomp a ha rho hrho hrrho0 hKO,
      ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
    have hlarge : rho * Real.exp (-s) ≤ rho :=
      mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
    exact (A.lowerDiskEnergy_mono hce Q hQ hei.isEmbedding hb hpos a hsmall
      ((ball_subset_ball hlarge).trans hball)).trans hs
  have hYint : Y ≤ C0 * ((∫ s in Icc (0 : ℝ) 1, A.lowerAngularEnergy a rho s) + rho ^ 2) := by
    have hi := integral_mono_ae (integrable_const Y)
      (((A.lowerAngularEnergy_integrable hce a hrho hKO).add (integrable_const (rho ^ 2))).const_mul
        C0) hYpoint
    have hleft : (∫ _ in Icc (0 : ℝ) 1, Y) = Y := by
      simp [integral_const, Real.volume_Icc, Measure.real]
    have hright : (∫ x in Icc (0 : ℝ) 1,
        C0 * (A.lowerAngularEnergy a rho x + rho ^ 2)) =
        C0 * ((∫ x in Icc (0 : ℝ) 1, A.lowerAngularEnergy a rho x) + rho ^ 2) := by
      rw [integral_const_mul, integral_add (A.lowerAngularEnergy_integrable hce a hrho hKO)
        (integrable_const (rho ^ 2))]
      simp [Real.volume_Icc, Measure.real]
    calc
      Y = ∫ _ in Icc (0 : ℝ) 1, Y := hleft.symm
      _ ≤ ∫ x in Icc (0 : ℝ) 1, C0 * (A.lowerAngularEnergy a rho x + rho ^ 2) := by
        simpa only [Pi.add_apply] using hi
      _ = C0 * ((∫ x in Icc (0 : ℝ) 1, A.lowerAngularEnergy a rho x) + rho ^ 2) := hright
  have hangular := A.lowerAngularEnergy_integral_le_annular_energy
    he hc0 Q hQ hei.isEmbedding hb hpos hC hcoercive a hrho hKO
  have hY : Y ≤ L * (X - Y) + C0 * rho ^ 2 :=
    hYint.trans ((mul_le_mul_of_nonneg_left (add_le_add hangular le_rfl) hC0.le).trans_eq
      (by dsimp [L, X, Y]; ring))
  change Y ≤ (L + 1) / (L + 2) * X + C0 / (L + 2) * rho ^ 2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ hL2).mpr
  nlinarith

end PoincareConjecture.M64ObservedWeakAnnulus
