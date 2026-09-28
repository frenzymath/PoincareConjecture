import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarHalfSpaceGradient
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev











set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential BoundaryLocalization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2





theorem halfSpace_H4_continuous_hessian {u : Plane → ℝ}
    (hc : HasCompactSupport u) (hu : MemWkp 4 2 u Half) :
    ∃ H : Fin 2 → Fin 2 → Plane → ℝ,
      (∀ i j, Continuous (H i j)) ∧
      ∀ i j, chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u Half) Half =ᵐ[
        volume.restrict Half] H i j := by
  let v (i j : Fin 2) : Plane → ℝ :=
    iteratedZeroExtension 2 Half (tsupport u) 2 ![i, j] u
  have hvc (i j : Fin 2) : HasCompactSupport (v i j) :=
    hasCompactSupport_iteratedZeroExtension hc (isClosed_tsupport u) (subset_refl _) 2 _
  have hv (i j : Fin 2) : MemWkp 2 2 (v i j) Half := by
    simpa only [v] using iteratedZeroExtension_memWkp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_halfSpace (isClosed_tsupport u)
      2 4 (by omega) ![i, j] hu (subset_refl _)
  have hvae (i j : Fin 2) : v i j =ᵐ[volume.restrict Half]
      chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u Half) Half := by
    have h := iteratedZeroExtension_ae_eq_iterWeakPartial
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_halfSpace (isClosed_tsupport u)
      2 4 (by omega) ![i, j] hu (subset_refl _)
    simpa only [v, iterWeakPartial_succ, iterWeakPartial_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one] using h
  choose H hHc hH using fun i j =>
    M64Uniformization.scalar_halfSpace_H2_continuous_extension (hvc i j) (hv i j)
  exact ⟨H, hHc, fun i j => (hvae i j).symm.trans (hH i j)⟩





theorem local_halfSpace_H4_continuous_hessian
    {V : Set Plane} (hV : IsOpen V)
    {u chi : Plane → ℝ} (hu : MemWkp 4 2 u (V ∩ Half))
    (hchi : ContDiff ℝ ∞ chi) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ V) :
    ∃ H : Fin 2 → Fin 2 → Plane → ℝ,
      (∀ i j, Continuous (H i j)) ∧
      ∀ i j, chosenWeakPartial' 2 j
        (chosenWeakPartial' 2 i (fun z => chi z * u z) Half) Half =ᵐ[
          volume.restrict Half] H i j := by
  have hcut : MemWkp 4 2 (fun z => chi z * u z) Half :=
    memWkp_mul_smooth_of_tsupport_subset 4 isOpen_halfSpace hV hu hchi hc hs
  exact halfSpace_H4_continuous_hessian hc.mul_right hcut

end PoincareConjecture.M64.RampTransport
