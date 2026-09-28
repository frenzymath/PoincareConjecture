import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedSphereSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FiniteSphereSideAllocation

set_option autoImplicit false
open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

theorem exists_original_excluded_sphere_balls {ι : Type*}
    (S : ι → Set V4) (e : ∀ i, S i ≃ₜ frontier Cube)
    (he : ∀ i, (e i).IsFinitePL) (hSS : ∀ i, S i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {U : Set Sphere} (hU : IsConnected U)
    (hmiss : ∀ i, Disjoint U ((Subtype.val : Sphere → V4) ⁻¹' S i))
    (hattach : ∀ i, (Subtype.val : Sphere → V4) ⁻¹' S i ⊆ closure U) :
    ∃ B : ι → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (S i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ S i)) ∧
        IsFinitePLBallPair V3 (Sphere \ (B i \ S i)) (S i)) ∧
      (∀ i, Disjoint ((Subtype.val : Sphere → V4) ⁻¹' B i) U) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (Subtype.val : Sphere → V4) '' closure U ⊆ Sphere \ ⋃ i, B i \ S i := by
  classical
  obtain ⟨p, hp⟩ := hU.nonempty
  have hpS (i : ι) : (p : V4) ∉ S i := fun hi => disjoint_left.mp (hmiss i) hp hi
  choose B hB hBS hpB hBo hBc using fun i =>
    exists_marked_sphere_sides (e i) (he i) (hSS i) p p.property (hpS i)
  have hBclosed (i : ι) : IsClosed ((Subtype.val : Sphere → V4) ⁻¹' B i) :=
    (hB i).isCompact.isClosed.preimage continuous_subtype_val
  have hBconn (i : ι) : IsPreconnected ((Subtype.val : Sphere → V4) ⁻¹' B i) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset (by simpa using hBS i)]
    exact (hB i).isConnected.isPreconnected
  have hBmiss (i : ι) : Disjoint ((Subtype.val : Sphere → V4) ⁻¹' B i) U := by
    rcases hU.isPreconnected.subset_rim_complement_or_complement
      (hBclosed i) (hBo i) (hmiss i) with hin | hout
    · exact False.elim (hpB i (hin hp).1)
    · exact disjoint_left.mpr fun _ hb hu => hout hu hb
  have hrne (i : ι) : ((Subtype.val : Sphere → V4) ⁻¹' S i).Nonempty := by
    have hh := (e i).isConnected_of_convex_frontier (isCompact_closedBall _ _)
      (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (by simp)
    obtain ⟨x, hx⟩ := hh.nonempty
    exact ⟨⟨x, hSS i hx⟩, hx⟩
  have hBdis := pairwise_disjoint_excluded_sides
    (fun i => (Subtype.val : Sphere → V4) ⁻¹' B i)
    (fun i => (Subtype.val : Sphere → V4) ⁻¹' S i)
    hBclosed hBconn hBo (fun i => preimage_mono (hB i).1) hrne hattach
    (fun i => (hBmiss i).mono_left sdiff_subset)
    (fun _ _ hij => (hdis hij).preimage Subtype.val)
  refine ⟨B, fun i => ⟨hB i, hBS i, hBo i, hBc i⟩, hBmiss, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    exact disjoint_left.mp (hBdis hij)
      (show (⟨x, hBS i hi⟩ : Sphere) ∈ (Subtype.val : Sphere → V4) ⁻¹' B i from hi) hj
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact closure_subset_complement_of_open_disjoint (hBo i)
      ((hBmiss i).mono_left sdiff_subset) hx hi

end Set
