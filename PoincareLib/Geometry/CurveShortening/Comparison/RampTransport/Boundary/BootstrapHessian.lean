import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.HalfSpaceGradient
import PoincareLib.Analysis.Sobolev.Boundary.Localization.Sobolev

/-!
# Continuous Hessian representatives from the actual half-space H4 map

The finite boundary bootstrap for MT Lemma 19.31, pp. 464-466, only needs
C2 up to the boundary before applying intrinsic comparison on trimmed
smooth annuli. Every second weak partial of a planar H4 map is H2 and
therefore has a continuous representative through the flat face.
Source: `derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`, Section 7.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareMT.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential BoundaryLocalization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

/-- The four second weak coordinate derivatives of a compactly supported
planar H4 function have continuous representatives through the flat face.
No zero-trace condition is used. Source: MT Lemma 19.31, pp. 464-466;
the finite boundary-bootstrap derivation, Section 7. -/
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

/-- Local H4 regularity gives continuous Hessian representatives after
any actual smooth cutoff supported in that neighborhood. The same
localized map appears in all four weak derivatives. Source: MT
Lemma 19.31, pp. 464-466; boundary-bootstrap derivation, Section 7. -/
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

end PoincareMT.M64.RampTransport
