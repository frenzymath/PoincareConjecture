import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Extension.Reflection
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives








set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryEmbedding

open Weak BoundaryTangential BoundaryExtension Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_subcritical {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ))
    {u : E → ℝ} (hc : HasCompactSupport u) (hu : MemW1p (ENNReal.ofReal p) u (halfSpace d)) :
    MemLp u (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
      (volume.restrict (halfSpace d)) := by
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hv : MemWkp 1 (ENNReal.ofReal p) (evenReflect u) univ :=
    MemWkp.one_iff_memW1p.mpr (memW1p_evenReflect hpe ENNReal.ofReal_ne_top hu)
  have hb := EuclideanEmbedding.EuclideanSubcritical.eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
    hp hpd isOpen_univ hv (hasCompactSupport_evenReflect hc) (subset_univ _)
  have hnorm : eLpNorm (evenReflect u)
      (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict univ) < ⊤ := by
    refine hb.trans_lt ?_
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top d))
      (wkpNorm_lt_top_of_memWkp hv)
  have hvq : MemLp (evenReflect u)
      (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume := by
    simpa only [Measure.restrict_univ] using
      (show MemLp (evenReflect u) _ (volume.restrict univ) from
        ⟨hv.memLp.aestronglyMeasurable, hnorm⟩)
  apply (hvq.restrict (halfSpace d)).ae_eq
  filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
  exact evenReflect_eq_on_halfSpace u hx


theorem memWkp_subcritical (k : ℕ) {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ))
    {u : E → ℝ} (hc : HasCompactSupport u)
    (hu : MemWkp (k + 1) (ENNReal.ofReal p) u {x : E | 0 < x 0}) :
    MemWkp k (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) u {x : E | 0 < x 0} := by
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hqe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) := by
    simpa only [ENNReal.ofReal_one, EuclideanEmbedding.TowerStep.pOne] using ENNReal.ofReal_le_ofReal
      (EuclideanEmbedding.TowerStep.pOne_ge_one hp hpd)
  induction k generalizing u with
  | zero => exact MemWkp.zero_iff_memLp.mpr (memLp_subcritical hp hpd hc hu.memW1p)
  | succ k ih =>
    let K := tsupport u
    let g (i : Fin d) := iteratedZeroExtension (ENNReal.ofReal p) (halfSpace d) K
      1 (fun _ : Fin 1 => i) u
    have hgc (i : Fin d) : HasCompactSupport (g i) :=
      hasCompactSupport_iteratedZeroExtension hc (isClosed_tsupport u) (subset_refl _) 1 _
    have hg (i : Fin d) : MemWkp (k + 1) (ENNReal.ofReal p) (g i) (halfSpace d) := by
      simpa using iteratedZeroExtension_memWkp hpe isOpen_halfSpace (isClosed_tsupport u)
        1 (k + 1 + 1) (by omega) (fun _ : Fin 1 => i) hu (subset_refl _)
    have hgae (i : Fin d) : g i =ᵐ[volume.restrict (halfSpace d)]
        chosenWeakPartial' (ENNReal.ofReal p) i u (halfSpace d) := by
      have h := iteratedZeroExtension_ae_eq_iterWeakPartial hpe isOpen_halfSpace
        (isClosed_tsupport u) 1 (k + 1 + 1) (by omega) (fun _ : Fin 1 => i) hu (subset_refl _)
      simpa only [iterWeakPartial_succ, iterWeakPartial_zero] using h
    apply memWkp_succ_of_weakDerivatives isOpen_halfSpace hqe
      (memLp_subcritical hp hpd hc hu.memW1p)
    · intro i
      exact (MemWkp_congr_ae hqe isOpen_halfSpace (hgae i)).mp (ih (hgc i) (hg i))
    · intro i
      exact chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i

end Poincare.Analysis.Sobolev.BoundaryEmbedding
