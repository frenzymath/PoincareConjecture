import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalBallPuncturedModel
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapParametrization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripBall









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem capDisk_inter_frontier
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (b : Bool) :
    P.capDisk b ∩ frontier R = P.capRimSet b := by
  apply Subset.antisymm
  · rintro x ⟨⟨z, hz, rfl⟩, hxf⟩
    exact ⟨z, ⟨(P.proper z (cap_source_subset b hz)).mp hxf, hz.2⟩, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    have hzfull := cap_source_subset b ⟨sphere_subset_closedBall hz.1, hz.2⟩
    exact ⟨⟨z, ⟨sphere_subset_closedBall hz.1, hz.2⟩, rfl⟩,
      (P.proper z hzfull).mpr hz.1⟩

theorem finitePL_cap_pair_in_realization
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f P.closedStrip) (b : Bool) :
    IsFinitePLBallPair (ℝ × ℝ) (f '' P.capDisk b) (f '' P.capRimSet b) := by
  have hpi : InjOn (P.capParameter b) (closedBall (0 : V2) 1) := by
    intro x hx y hy hxy
    have hh : (⟨x, hx⟩ : closedBall (0 : V2) 1) = ⟨y, hy⟩ :=
      (P.embedding_capParameter b).injective hxy
    exact congrArg Subtype.val hh
  have hpstrip : MapsTo (P.capParameter b) (closedBall (0 : V2) 1) P.closedStrip := by
    intro x hx
    exact ⟨(x, if b then (1 / 2 : ℝ) else -(1 / 2)),
      ⟨hx, by cases b <;> norm_num⟩, rfl⟩
  have hp := finitePLBallPair_original_image (isFinitePLBallPair_unit_cube (ι := Fin 2))
    (P.polyhedral_capParameter b) subset_rfl hpi hpstrip hf hfi
  rw [P.capParameter_image_disk, P.capParameter_image_rim] at hp
  exact hp.model_equiv (ContinuousLinearEquiv.ofFinrankEq (by simp) : V2 ≃L[ℝ] (ℝ × ℝ))

theorem exists_closedStrip_single_hole_model
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f P.closedStrip) :
    ∃ (G : P.closedStrip ≃ₜ (f '' P.closedStrip))
      (C : (f '' P.closedStrip) ≃ₜ
        (Geometry.CubicalThreeSphere.sphere \
          (Geometry.CubicalThreeSphere.upper \ Geometry.CubicalThreeSphere.seam) : Set (Fin 4 → ℝ))),
      (∀ x : P.closedStrip, (G x : E) = f x) ∧ C.IsFinitePL ∧
      (∀ x : P.closedStrip,
        (x : X) ∈ (P.map '' (Rim ×ˢ J)) ∪ P.endDisks ↔
          (C (G x) : Fin 4 → ℝ) ∈ Geometry.CubicalThreeSphere.seam) ∧
      (∀ x : P.closedStrip, (x : X) ∈ frontier P.closedStrip ↔
        (C (G x) : Fin 4 → ℝ) ∈ Geometry.CubicalThreeSphere.seam) ∧
      (fun x : P.closedStrip => (C (G x) : Fin 4 → ℝ)) ''
        ((Subtype.val : P.closedStrip → X) ⁻¹' ((P.map '' (Rim ×ˢ J)) ∪ P.endDisks)) =
          Geometry.CubicalThreeSphere.seam := by
  obtain ⟨b⟩ := P.exists_closedStrip_ball
  exact b.exists_single_hole_marked_model f hf hfi

theorem closedStrip_hasPuncturedSphereModel
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f P.closedStrip) : HasPuncturedSphereModel e f P.closedStrip := by
  obtain ⟨b⟩ := P.exists_closedStrip_ball
  exact b.hasPuncturedSphereModel f hf hfi

end PoincareConjecture.M76.OriginalDiskProduct
