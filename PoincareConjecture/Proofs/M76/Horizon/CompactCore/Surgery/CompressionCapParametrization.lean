import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductSlices

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {L : Set X} {j : V2 → X}

noncomputable def capParameter (P : OriginalDiskProduct e L j) (b : Bool) : V2 → X :=
  P.slice (if b then (1 / 2 : ℝ) else -(1 / 2))

theorem capParameter_apply (P : OriginalDiskProduct e L j) (b : Bool) (z : V2) :
    P.capParameter b z = P.map (z, if b then (1 / 2 : ℝ) else -(1 / 2)) := rfl

theorem polyhedral_capParameter (P : OriginalDiskProduct e L j) (b : Bool) :
    PolyhedralPLInCharts e (P.capParameter b) D :=
  P.polyhedral_slice (by cases b <;> norm_num)

theorem embedding_capParameter (P : OriginalDiskProduct e L j) (b : Bool) :
    Topology.IsEmbedding (fun z : D => P.capParameter b z) :=
  P.embedding_slice (by cases b <;> norm_num)

theorem capParameter_image_disk (P : OriginalDiskProduct e L j) (b : Bool) :
    P.capParameter b '' D = P.capDisk b := P.slice_image _

theorem capParameter_image_rim (P : OriginalDiskProduct e L j) (b : Bool) :
    P.capParameter b '' Q = P.capRimSet b := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(z, if b then (1 / 2 : ℝ) else -(1 / 2)), ⟨hz, rfl⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
    refine ⟨z.1, hz.1, ?_⟩
    change P.map (z.1, if b then (1 / 2 : ℝ) else -(1 / 2)) = P.map z
    rw [← ht]

theorem capParameter_mem_rim_iff (P : OriginalDiskProduct e L j) (b : Bool) (z : D) :
    P.capParameter b z ∈ P.capRimSet b ↔ (z : V2) ∈ Q := by
  constructor
  · rintro ⟨w, hw, hweq⟩
    have hwfull := cap_source_subset b ⟨sphere_subset_closedBall hw.1, hw.2⟩
    have hzfull := cap_source_subset b
      (show ((z : V2), if b then (1 / 2 : ℝ) else -(1 / 2)) ∈
        D ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)} from ⟨z.property, rfl⟩)
    have heq := congrArg Prod.fst (P.injective hwfull hzfull hweq)
    change w.1 = (z : V2) at heq
    exact heq ▸ hw.1
  · intro hz
    exact ⟨((z : V2), if b then (1 / 2 : ℝ) else -(1 / 2)), ⟨hz, rfl⟩, rfl⟩

theorem capParameter_mem_frontier_iff (P : OriginalDiskProduct e L j) (b : Bool) (z : D) :
    P.capParameter b z ∈ frontier L ↔ (z : V2) ∈ Q :=
  P.slice_proper (by cases b <;> norm_num) z

theorem exists_capParameter_homeomorph (P : OriginalDiskProduct e L j) (b : Bool) :
    ∃ H : D ≃ₜ P.capDisk b,
      (∀ z : D, (H z : X) = P.capParameter b z) ∧
      ∀ z : D, (H z : X) ∈ P.capRimSet b ↔ (z : V2) ∈ Q := by
  have hrange : range (fun z : D => P.capParameter b z) = P.capDisk b := by
    rw [← P.capParameter_image_disk b]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let H : D ≃ₜ P.capDisk b :=
    (P.embedding_capParameter b).toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨H, fun _ => rfl, ?_⟩
  exact P.capParameter_mem_rim_iff b

end PoincareConjecture.M76.OriginalDiskProduct
