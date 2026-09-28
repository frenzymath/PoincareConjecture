import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.ZeroExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.Supercritical
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Sobolev.BoundaryEmbedding

open Weak BoundaryTangential Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_continuous_representative {p : ℝ} (hpd : (d : ℝ) < p)
    {u : E → ℝ} (hc : HasCompactSupport u) (hu : MemW1p (ENNReal.ofReal p) u univ) :
    ∃ F : E → ℝ, Continuous F ∧ u =ᵐ[volume] F := by
  obtain ⟨R, hR, hKR⟩ := hc.isBounded.subset_ball_lt 0 (0 : E)
  obtain ⟨χ, hχ, hχc, _, hχone, hχs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hc Metric.isOpen_ball hKR
  have huB : MemWkp 1 (ENNReal.ofReal p) u (Metric.ball (0 : E) (4 * R)) :=
    MemWkp.one_iff_memW1p.mpr (Euclidean.MemW1p.mono_set Metric.isOpen_ball (subset_univ _) hu)
  obtain ⟨F, hF, hFu⟩ := EuclideanMorrey.morrey_iteratedFDeriv_representative
    hpd (by positivity : 0 < 4 * R) 0 huB
  have hχu (x : E) : χ x * u x = u x := by
    by_cases hx : u x = 0
    · simp [hx]
    · rw [hχone x (subset_tsupport u hx), one_mul]
  have hball : Metric.ball (0 : E) (4 * R / 4) = Metric.ball (0 : E) R := by congr 1; ring
  rw [hball] at hFu
  have hFu' : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : E) R → u x = F x :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hFu
  refine ⟨fun x => χ x * F x, hχ.continuous.mul hF.continuous, ?_⟩
  filter_upwards [hFu'] with x hx
  by_cases hxB : x ∈ Metric.ball (0 : E) R
  · rw [← hx hxB, hχu]
  · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hKR h))
    have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxB (hχs h))
    simp [hu0, hχ0]

private theorem eq_zero_on_closed_lower_halfSpace {F u : E → ℝ}
    (hF : Continuous F) (hae : (halfSpace d).indicator u =ᵐ[volume] F) :
    ∀ x : E, x 0 ≤ 0 → F x = 0 := by
  let L : Set E := {x | x 0 < 0}
  have hL : IsOpen L := isOpen_lt (by fun_prop) continuous_const
  have heq : EqOn F (fun _ => 0) L := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hL hF.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae hae.symm,
      ae_restrict_mem hL.measurableSet] with x hx hxL
    rw [hx, indicator_of_notMem]
    exact not_lt.mpr (le_of_lt (show x 0 < 0 from hxL))
  intro x hx
  apply heq.closure hF continuous_const
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let y : E := x - (ε / 2) • EuclideanSpace.single (0 : Fin d) 1
  refine ⟨y, ?_, ?_⟩
  · change (x - (ε / 2) • EuclideanSpace.single (0 : Fin d) 1 : E) 0 < 0
    simpa using sub_neg.mpr (lt_of_le_of_lt hx (div_pos hε (by norm_num : (0 : ℝ) < 2)))
  · change dist x (x - (ε / 2) • EuclideanSpace.single (0 : Fin d) 1) < ε
    rw [dist_self_sub_right, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (div_pos hε (by norm_num : (0 : ℝ) < 2))]
    linarith



theorem exists_continuous_zero_extension {u : E → ℝ} (hc : HasCompactSupport u)
    (hu0 : MemW01p 2 u {x : E | 0 < x 0})
    (hu : MemWkp (d + 1) 2 u {x : E | 0 < x 0}) :
    ∃ F : E → ℝ, Continuous F ∧
      ({x : E | 0 < x 0}.indicator u =ᵐ[volume] F) ∧
      ∀ x : E, x 0 ≤ 0 → F x = 0 := by
  obtain ⟨p, hp, hpd, hup⟩ := exists_supercritical_memW1p hc hu
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hz := memW1p_zeroExtension hpe hu0 hup
  have hzc : HasCompactSupport ((halfSpace d).indicator u) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    apply subset_tsupport u
    change u x ≠ 0
    intro hux
    by_cases hxH : x ∈ halfSpace d <;> simp [hxH, hux] at hx
  obtain ⟨F, hF, hFu⟩ := exists_continuous_representative hpd hzc hz
  exact ⟨F, hF, hFu, eq_zero_on_closed_lower_halfSpace hF hFu⟩

end Poincare.Analysis.Sobolev.BoundaryEmbedding
