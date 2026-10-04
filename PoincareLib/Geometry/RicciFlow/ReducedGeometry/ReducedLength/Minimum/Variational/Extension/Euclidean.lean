import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Jets
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Pasting

/-!
Adapted from Mapher `Proofs/M08/SmoothEndpointExtension.lean`, commit
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.ReducedLengthMinimum.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_extension_Icc {a b : ℝ} (hab : a < b)
    (f : ℝ → E) (hf : ContDiffOn ℝ ∞ f (Icc a b)) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ EqOn g f (Icc a b) := by
  obtain ⟨L, hL, hLa⟩ := exists_smooth_endpoint_jets
    (fun k ↦ iteratedDerivWithin k f (Icc a b) a)
  obtain ⟨R, hR, hRb⟩ := exists_smooth_endpoint_jets
    (fun k ↦ iteratedDerivWithin k f (Icc a b) b)
  apply smooth_pasting_of_matching_endpoint_jets hab f
    (fun x ↦ L (x - a)) (fun x ↦ R (x - b)) hf
    (hL.comp (contDiff_id.sub contDiff_const)) (hR.comp (contDiff_id.sub contDiff_const))
  · intro k
    simpa only [iteratedDeriv_comp_sub_const, sub_self] using hLa k
  · intro k
    simpa only [iteratedDeriv_comp_sub_const, sub_self] using hRb k

end PoincareMT.ReducedLengthMinimum.Variational

