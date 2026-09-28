import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {T : ℝ} (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
  (old : SurgeryTerminalStrongNeck F T hT i)



theorem source_initial_old_scalar_bounds
    (hsmall : F.parameters.delta T ≤ 1 / 200) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    {x : (F.event T hT).terminal.carrier} (hx : x ∈ ((F.event T hT).necks i).neck.carrier) :
    (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) / 4 <
        (F.connection (T + s / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2))).scalarCurvature
          (old.cylinder.forward s hs x) ∧
      (F.connection (T + s / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2))).scalarCurvature
          (old.cylinder.forward s hs x) ≤ 2 * (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) := by
  let q := ((F.event T hT).necks i).neck.scale⁻¹ ^ 2
  let R := (F.connection (T + s / q)).scalarCurvature (old.cylinder.forward s hs x)
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr ((F.event T hT).necks i).neck.scale_pos)
  have herr : |R / q - 1 / (1 - s)| ≤ (16 / 5 : ℝ) * F.parameters.delta T :=
    source_initial_old_scalar_difference_le hT i old hsmall s hs hx
  have hden : 0 < 1 - s := by linarith only [hs.2]
  have hlo : (1 / 2 : ℝ) < 1 / (1 - s) :=
    (lt_div_iff₀ hden).mpr (by linarith only [hs.1])
  have hhi : 1 / (1 - s) ≤ (1 : ℝ) :=
    (div_le_iff₀ hden).mpr (by linarith only [hs.2])
  have hlow : (1 / 4 : ℝ) < R / q := by
    have h := (abs_le.mp herr).1
    linarith only [h, hlo, hsmall]
  have hhigh : R / q ≤ (2 : ℝ) := by
    have h := (abs_le.mp herr).2
    linarith only [h, hhi, hsmall]
  refine ⟨?_, (div_le_iff₀ hq).mp hhigh⟩
  have h := (lt_div_iff₀ hq).mp hlow
  change q / 4 < R
  linarith only [h]



theorem source_initial_axial_slice
    (hsmall : F.parameters.delta T ≤ 1 / 200) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    {B : ℝ} (hB : 0 < B) :
    let N := ((F.event T hT).necks i).neck
    let U := old.cylinder.forward s hs '' N.region (-B) B
    IsOpen U ∧ U.Nonempty ∧
      (∀ x ∈ U, old.cylinder.inverse s hs x ∈ N.region (-B) B ∧
        old.cylinder.forward s hs (old.cylinder.inverse s hs x) = x) ∧
      ∀ x ∈ U, (F.connection (T + s / (N.scale⁻¹ ^ 2))).scalarCurvature x ≤
        2 * (N.scale⁻¹ ^ 2) := by
  let N := ((F.event T hT).necks i).neck
  let chart := M44.cylinderSliceChart old.cylinder N.carrier_open s hs
  have hsub : N.region (-B) B ⊆ N.carrier := fun _ hx => hx.1
  have hcenter : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hheight : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem hcenter).mp N.center_on_central_sphere
  have hcenterV : N.center ∈ N.region (-B) B :=
    ⟨hcenter, by rw [hheight]; exact ⟨neg_neg_of_pos hB, hB⟩⟩
  refine ⟨chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source (N.region_isOpen _ _) hsub,
    ⟨_, mem_image_of_mem _ hcenterV⟩, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [old.cylinder.left_inverse s hs hy.1]
    exact ⟨hy, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact (source_initial_old_scalar_bounds hT i old hsmall s hs hy.1).2

end PoincareConjecture.M47
