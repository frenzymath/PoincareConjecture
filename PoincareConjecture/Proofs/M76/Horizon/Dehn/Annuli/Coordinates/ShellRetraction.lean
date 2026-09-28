import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Coordinates.RetainedShell
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.Projection

set_option autoImplicit false
open Set Metric Geometry Topology NormedSpace

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

local notation "U" => chartShell L retained
local notation "pi" => hamiltonMarkedProjection (Fin 1) (Fin 2) L

theorem chartShell_inverse_mem_projection_target (z : U) :
    (e retained.index).symm (z : V3) ∈ retained.projectionChart.target := by
  obtain ⟨v, hv, hve⟩ := z.property.2.2
  exact ⟨(((e retained.index).symm z).1, v),
    ⟨mem_univ _, mem_ball_zero_iff.mpr hv.2⟩, Prod.ext rfl hve⟩

noncomputable def chartShellSource : C(U, V1 × V2) where
  toFun z := retained.projectionChart.symm ((e retained.index).symm (z : V3))
  continuous_toFun := retained.projectionChart.symm.continuousOn.comp_continuous
    ((e retained.index).symm.continuousOn.comp_continuous continuous_subtype_val
      (fun z ↦ z.property.1)) (chartShell_inverse_mem_projection_target L retained)

theorem chartShellSource_transverse (z : U) :
    1 < ‖(chartShellSource L retained z).2‖ ∧ ‖(chartShellSource L retained z).2‖ < 2 := by
  obtain ⟨v, hv, hve⟩ := z.property.2.2
  let x : V1 × V2 := (((e retained.index).symm z).1, v)
  have hx : x ∈ retained.projectionChart.source :=
    ⟨mem_univ _, mem_ball_zero_iff.mpr hv.2⟩
  have heq : retained.projectionChart x = (e retained.index).symm z := Prod.ext rfl hve
  change 1 < ‖(retained.projectionChart.symm ((e retained.index).symm z)).2‖ ∧
    ‖(retained.projectionChart.symm ((e retained.index).symm z)).2‖ < 2
  rw [← heq, retained.projectionChart.left_inv hx]
  exact hv

private theorem chartShellSource_transverse_ne_zero (z : U) :
    (chartShellSource L retained z).2 ≠ 0 := by
  intro heq
  have hp := (chartShellSource_transverse L retained z).1
  rw [heq, norm_zero] at hp
  linarith

noncomputable def chartShellRadial : C(U, Q2) where
  toFun z := ⟨normalize (chartShellSource L retained z).2,
    mem_sphere_zero_iff_norm.mpr (norm_normalize
      (chartShellSource_transverse_ne_zero L retained z))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ContinuousAt.comp (f := fun z : U ↦ (chartShellSource L retained z).2)
      (continuousAt_normalize_of_ne_zero (chartShellSource_transverse_ne_zero L retained z))
      (continuous_snd.comp (chartShellSource L retained).continuous).continuousAt

theorem chartShellRadial_prescribed
    {z : U} (b : Bool) (u : Q2)
    (hz : (z : V3) = h (coordinates (endpoint b, u))) :
    chartShellRadial L retained z = u := by
  have hsourceShell : coordinates (endpoint b, (u : V2)) ∈ sourceShell :=
    coordinates_mem_sourceShell ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩
  have hwindow : coordinates (endpoint b, (u : V2)) ∈ retained.projectionChart.source :=
    ⟨mem_univ _, mem_ball_zero_iff.mpr hsourceShell.2.2⟩
  apply Subtype.ext
  change normalize (retained.projectionChart.symm ((e retained.index).symm z)).2 = (u : V2)
  rw [hz, chartShell_inverse_formula L retained hsourceShell,
    ← retained.projectionChart_apply, retained.projectionChart.left_inv hwindow]
  change normalize ((3 / 2 : ℝ) • (u : V2)) = (u : V2)
  rw [normalize_smul_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp u.property)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
