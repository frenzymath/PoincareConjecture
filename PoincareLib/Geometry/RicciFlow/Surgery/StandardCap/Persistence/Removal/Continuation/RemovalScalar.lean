import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Cylinder.CylinderCurvature

/-!
# Physical scalar bounds for the whole tracked birth ball

The normalized ordinary flow covers the whole birth-chart target.
Its scalar bound therefore gives the physical cylinder bound in
birth-height units used by the terminal removal assembly.
Morgan--Tian, Lemma 16.8 and Claim 16.10, pp. 373-375;
M44 derivation 79.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M44.CylinderRicciFlow

local notation "E" => StandardCapSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- A normalized scalar bound controls every original physical
cylinder line, using the full birth-chart target. Source:
Claim 16.10, pp. 374-375; M44 derivation 79. -/
theorem physical_scalar_le
    {e : SurgeryFlowCylinder F C origin scale I U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f) (hU : IsOpen U) (htarget : f.target = U)
    {s : ℝ} (hs : s ∈ I) {K : ℝ}
    (hbound : ∀ y, (G.flow.connection s).scalarCurvature y ≤ K)
    {x : C.carrier} (hx : x ∈ U) :
    (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤
      K * scale := by
  let y : (⟨f.target, f.open_target⟩ : Opens C.carrier) := ⟨x, htarget.symm ▸ hx⟩
  have hb := hbound y
  rw [G.scalar_eq hU (fun _ hz => htarget ▸ hz) s hs y] at hb
  change (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) / scale ≤ K
    at hb
  exact (div_le_iff₀ e.scale_pos).mp hb

/-- At the actual inverse-square birth normalization the physical
bound is exactly `K / h^2`. Source: Claim 16.10, pp. 374-375;
M44 derivation 79. -/
theorem physical_scalar_le_height {h : ℝ}
    {e : SurgeryFlowCylinder F C origin (h⁻¹ ^ 2) I U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f) (hU : IsOpen U) (htarget : f.target = U)
    {s : ℝ} (hs : s ∈ I) {K : ℝ}
    (hbound : ∀ y, (G.flow.connection s).scalarCurvature y ≤ K)
    {x : C.carrier} (hx : x ∈ U) :
    (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤
      K / h ^ 2 := by
  simpa only [inv_pow, div_eq_mul_inv] using G.physical_scalar_le hU htarget hs hbound hx

end PoincareMT.M44.CylinderRicciFlow
