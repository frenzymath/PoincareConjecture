import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarHalfSpaceGradient
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
private def scalarHalfSpace : Set Plane := {x | 0 < x.ofLp 0}
local notation "Half" => scalarHalfSpace

open Poincare.Analysis.Sobolev
open Weak Euclidean
open BoundaryTangential BoundaryLocalization

theorem exists_continuous_halfSpace_gradient_of_local_H3
    {V : Set Plane} (hV : IsOpen V)
    {u : Plane → ℝ} (hu : MemWkp 3 2 u (V ∩ Half))
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ V) :
    ∃ G : Fin 2 → Plane → ℝ,
      (∀ i, Continuous (G i)) ∧
      ∀ i, chosenWeakPartial' 2 i (fun z => χ z * u z) Half =ᵐ[
        volume.restrict Half] G i := by
  have hH : IsOpen Half := by
    exact isOpen_lt continuous_const (by fun_prop)
  have hcut : MemWkp 3 2 (fun z => χ z * u z) Half :=
    memWkp_mul_smooth_of_tsupport_subset 3 hH hV hu hχ hc hs
  have hcompact : HasCompactSupport (fun z => χ z * u z) := hc.mul_right
  exact scalar_halfSpace_H3_continuous_gradient hcompact hcut

end PoincareConjecture.M64Uniformization
