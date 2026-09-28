import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialEnergy













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

namespace M64ObservedWeakAnnulus



theorem lower_disk_energy_le_column_bound
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {B : ℝ} (hB : ∀ q, ‖Q q‖ ≤ B)
    (a : LoopPlane) (r : ℝ) (hball : ball a r ⊆ O) :
    A.lowerDiskEnergy Q a r ≤
      (B / 2) * ((∫ p in ball a r, ‖A.lowerExtensionColumn 0 p‖ ^ 2) +
        (∫ p in ball a r, ‖A.lowerExtensionColumn 1 p‖ ^ 2)) := by
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hB0 : 0 ≤ B := by
    exact (norm_nonneg (Q (A.lowerExtensionMap 0))).trans (hB _)
  have hEint := (A.lower_energy_integrable hce Q hQ hei hB).mono_set hball
  have hcolint (i : Fin 2) :
      IntegrableOn (fun p => ‖A.lowerExtensionColumn i p‖ ^ 2) (ball a r) volume := by
    have hM := ((A.lower_extension_memLp hce).2 i).mono_measure
      (Measure.restrict_mono hball le_rfl)
    exact (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mp hM
  unfold lowerDiskEnergy
  calc
    _ ≤ ∫ p in ball a r, (B / 2) *
        (‖A.lowerExtensionColumn 0 p‖ ^ 2 + ‖A.lowerExtensionColumn 1 p‖ ^ 2) := by
      apply integral_mono_ae hEint
        (((hcolint 0).add (hcolint 1)).const_mul (B / 2))
      filter_upwards [] with p
      have hq0 := (Q (A.lowerExtensionMap p)).le_opNorm₂
        (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p)
      have hq1 := (Q (A.lowerExtensionMap p)).le_opNorm₂
        (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)
      have hm0 := mul_le_mul_of_nonneg_right (hB (A.lowerExtensionMap p))
        (sq_nonneg ‖A.lowerExtensionColumn 0 p‖)
      have hm1 := mul_le_mul_of_nonneg_right (hB (A.lowerExtensionMap p))
        (sq_nonneg ‖A.lowerExtensionColumn 1 p‖)
      have hq0' : Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p)
          (A.lowerExtensionColumn 0 p) ≤ B * ‖A.lowerExtensionColumn 0 p‖ ^ 2 := by
        rw [Real.norm_eq_abs] at hq0
        nlinarith [le_abs_self (Q (A.lowerExtensionMap p)
          (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p))]
      have hq1' : Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p)
          (A.lowerExtensionColumn 1 p) ≤ B * ‖A.lowerExtensionColumn 1 p‖ ^ 2 := by
        rw [Real.norm_eq_abs] at hq1
        nlinarith [le_abs_self (Q (A.lowerExtensionMap p)
          (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p))]
      change (Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p)
          (A.lowerExtensionColumn 0 p) +
          Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p)
            (A.lowerExtensionColumn 1 p)) / 2 ≤
        B / 2 * (‖A.lowerExtensionColumn 0 p‖ ^ 2 +
          ‖A.lowerExtensionColumn 1 p‖ ^ 2)
      nlinarith [hq0', hq1']
    _ = _ := by
      rw [integral_const_mul, integral_add (hcolint 0) (hcolint 1)]

end M64ObservedWeakAnnulus

end PoincareConjecture
