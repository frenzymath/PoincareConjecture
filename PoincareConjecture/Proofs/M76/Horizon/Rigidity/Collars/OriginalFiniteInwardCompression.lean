import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteCollarModel










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.OriginalFiniteCollarModel

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

theorem collarHomeomorph_isFinitePL (M : OriginalFiniteCollarModel e R) :
    M.collarHomeomorph.IsFinitePL := by
  let E := M.collarVertices → ℝ × V3
  let z : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hz : FinitePiecewiseAffineOn z M.collarBase.space :=
    (M.collarBase.affineOnFaces_affine z).finitePiecewiseAffineOn M.collar_finite
  exact ⟨fun x => M.collar (x, 0),
    M.collar_pl.comp hz (fun _ hx => ⟨hx, le_rfl, zero_le_one⟩),
    fun x => (M.collar_zero x).symm⟩



theorem exists_inward_compression (M : OriginalFiniteCollarModel e R) :
    ∃ (D : Set (M.vertices → ℝ × V3)) (H : M.complex.space ≃ₜ D),
      H.IsFinitePL ∧ D ⊆ M.complex.space ∧ Disjoint D M.boundary.space ∧
      (∀ x : M.collarBase.space,
        (H ⟨M.collarHomeomorph x,
          SimplicialComplex.space_subset_of_le M.boundary_le
            (M.collarHomeomorph x).property⟩ : M.vertices → ℝ × V3) =
          M.collar ((x : M.collarVertices → ℝ × V3), 1 / 2)) ∧
      ∀ z ∈ M.collarBase.space ×ˢ I,
        M.collar z ∈ D ↔ (1 / 2 : ℝ) ≤ z.2 := by
  obtain ⟨D, H, hH, hDK, hHvalue, _, hclear⟩ :=
    Dehn.exists_inward_collar_compression M.complex M.collarBase M.finite
      M.collar_finite M.collar M.collar_pl M.collar_injective M.collar_inside M.collar_open
  have hDA : Disjoint D M.boundary.space := by
    apply Set.disjoint_left.mpr
    intro y hyD hyA
    obtain ⟨x, hx⟩ := M.collarHomeomorph.surjective ⟨y, hyA⟩
    have hc : M.collar ((x : M.collarVertices → ℝ × V3), 0) = y :=
      (M.collar_zero x).trans (congrArg Subtype.val hx)
    have h := (hclear _ ⟨x.property, le_rfl, zero_le_one⟩).mp (hc.symm ▸ hyD)
    norm_num at h
  refine ⟨D, H, hH, hDK, hDA, ?_, hclear⟩
  intro x
  have h := hHvalue ((x : M.collarVertices → ℝ × V3), 0)
    ⟨x.property, le_rfl, zero_le_one⟩
  have hp : (⟨M.collar ((x : M.collarVertices → ℝ × V3), 0),
      M.collar_inside ⟨x.property, le_rfl, zero_le_one⟩⟩ : M.complex.space) =
      ⟨M.collarHomeomorph x, SimplicialComplex.space_subset_of_le M.boundary_le
        (M.collarHomeomorph x).property⟩ := Subtype.ext (M.collar_zero x)
  rw [hp] at h
  simpa only [zero_add] using h

end PoincareConjecture.M76.OriginalFiniteCollarModel
