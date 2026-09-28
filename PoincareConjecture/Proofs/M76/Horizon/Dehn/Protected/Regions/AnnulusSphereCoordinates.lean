import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.ChartSphereImage
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.SphereLocalFlatness
import PoincareConjecture.Proofs.M76.Brown.LocallyFlatBoundedRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.Projection

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V1 × V2)
local notation "D1" => closedBall (0 : V1) 1
local notation "Q1" => sphere (0 : V1) 1
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  (T : HamiltonProtectedDehnAnnulus L e)

local notation "pi" => hamiltonMarkedProjection (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L

def sphereSet : Set (LatticeHandleAmbient (Fin 1) (Fin 2) L) :=
  T.surface ∪ hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2)

def sourceSphere : Set E :=
  (D1 ×ˢ closedBall (0 : V2) 2) ∩ pi ⁻¹' sphereSet L T

def sourceProtectedAnnulus : Set E :=
  (D1 ×ˢ closedBall (0 : V2) 2) ∩ pi ⁻¹' T.surface

theorem sourceProtectedAnnulus_inside :
    sourceProtectedAnnulus L T ⊆ (D1 ×ˢ closedBall (0 : V2) 2) \
      (D1 ×ˢ closedBall (0 : V2) 1) :=
  fun x hx ↦ ⟨hx.1, fun hxcore ↦ (T.inside hx.2).2 ⟨x, hxcore, rfl⟩⟩

theorem sphereSet_subset_block :
    sphereSet L T ⊆ hamiltonHandleBlock (Fin 1) (Fin 2) L 2 := by
  intro y hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · exact (T.inside hy).1
  · exact ⟨x, ⟨sphere_subset_closedBall hx.1,
      closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hx.2⟩, rfl⟩

theorem sphereSet_old_boundary :
    sphereSet L T ∩ frontier R = hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2) := by
  apply Subset.antisymm
  · intro y hy
    rcases hy.1 with hyT | hyA
    · let x := T.parametrization.symm ⟨y, hyT⟩
      have hpx : (T.parametrization x : LatticeHandleAmbient (Fin 1) (Fin 2) L) = y :=
        congrArg Subtype.val (T.parametrization.apply_symm_apply ⟨y, hyT⟩)
      have hxQ : (x : E).1 ∈ Q1 := (T.old_boundary_iff x).mp (hpx.symm ▸ hy.2)
      have hval : y = pi ((x : E).1, (3 / 2 : ℝ) • (x : E).2) := by
        rw [← hpx, ← T.map_eq x]
        exact T.boundary_values x ⟨hxQ, x.property.2⟩
      refine ⟨((x : E).1, (3 / 2 : ℝ) • (x : E).2), ⟨hxQ, ?_⟩, hval.symm⟩
      rw [mem_closedBall_zero_iff, norm_smul, mem_sphere_zero_iff_norm.mp x.property.2]
      norm_num
    · exact hyA
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨Or.inr ⟨x, hx, rfl⟩, ?_⟩
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hx.1, mem_univ _⟩

variable {h : OpenPartialHomeomorph E V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

include retained

theorem sourceProtectedAnnulus_outer_open :
    sourceProtectedAnnulus L T ⊆ D1 ×ˢ ball (0 : V2) 2 := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := T.inside_outer_open hx.2
  exact retained.quotient_injective ⟨hy.1, ball_subset_closedBall hy.2⟩ hx.1 heq ▸ hy

theorem sourceSphere_old_boundary :
    sourceSphere L T ∩ frontier (D1 ×ˢ (univ : Set V2)) =
      Q1 ×ˢ closedBall (0 : V2) (3 / 2) := by
  apply Subset.antisymm
  · intro x hx
    have hpi := (hamiltonMarkedProjection_mem_frontier (L := L) x).mpr hx.2
    obtain ⟨y, hy, heq⟩ := (sphereSet_old_boundary L T).subset ⟨hx.1.2, hpi⟩
    have hy2 : y ∈ D1 ×ˢ closedBall (0 : V2) 2 :=
      ⟨sphere_subset_closedBall hy.1,
        closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hy.2⟩
    exact retained.quotient_injective hy2 hx.1.1 heq ▸ hy
  · intro x hx
    refine ⟨⟨⟨sphere_subset_closedBall hx.1,
      closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hx.2⟩,
      Or.inr ⟨x, hx, rfl⟩⟩, ?_⟩
    rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hx.1, mem_univ _⟩

theorem sourceSphere_decomposition :
    sourceSphere L T = sourceProtectedAnnulus L T ∪
      (Q1 ×ˢ closedBall (0 : V2) (3 / 2)) := by
  apply Subset.antisymm
  · intro x hx
    rcases hx.2 with hxK | hxA
    · exact Or.inl ⟨hx.1, hxK⟩
    · obtain ⟨y, hy, heq⟩ := hxA
      have hy2 : y ∈ D1 ×ˢ closedBall (0 : V2) 2 :=
        ⟨sphere_subset_closedBall hy.1,
          closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hy.2⟩
      exact Or.inr (retained.quotient_injective hy2 hx.1 heq ▸ hy)
  · rintro x (hx | hx)
    · exact ⟨hx.1, Or.inl hx.2⟩
    · exact ((sourceSphere_old_boundary L T retained).symm.subset hx).1

theorem sourceProtectedAnnulus_old_boundary :
    sourceProtectedAnnulus L T ∩ (Q1 ×ˢ (univ : Set V2)) ⊆
      Q1 ×ˢ closedBall (0 : V2) (3 / 2) := by
  intro x hx
  apply (sourceSphere_old_boundary L T retained).subset
  refine ⟨⟨hx.1.1, Or.inl hx.1.2⟩, ?_⟩
  simpa only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] using hx.2

theorem sphereSet_subset_chart : sphereSet L T ⊆ (e retained.index).source := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := sphereSet_subset_block L T hy
  exact retained.contains x hx

theorem sourceSphere_image_eq
    (hsource : D1 ×ˢ (univ : Set V2) ⊆ h.source) :
    h.symm '' ((e retained.index) '' sphereSet L T) = sourceSphere L T := by
  apply Subset.antisymm
  · rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := sphereSet_subset_block L T hy
    rw [retained.formula z hz, h.left_inv (hsource ⟨hz.1, mem_univ _⟩)]
    exact ⟨hz, hy⟩
  · intro x hx
    refine ⟨(e retained.index) (pi x), ⟨pi x, hx.2, rfl⟩, ?_⟩
    rw [retained.formula x hx.1, h.left_inv (hsource ⟨hx.1.1, mem_univ _⟩)]

omit retained in
theorem sourceProtectedAnnulus_isCompact [DiscreteTopology L] :
    IsCompact (sourceProtectedAnnulus L T) := by
  let : CompactSpace (D1 ×ˢ Q2) := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
  let : CompactSpace T.surface := T.parametrization.compactSpace
  have hT : IsCompact T.surface := isCompact_iff_compactSpace.mpr inferInstance
  exact ((isCompact_closedBall (0 : V1) 1).prod (isCompact_closedBall (0 : V2) 2)).inter_right
    (hT.isClosed.preimage continuous_hamiltonMarkedProjection)

omit retained in
theorem sourceProtectedAnnulus_projection : pi '' sourceProtectedAnnulus L T = T.surface := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (T.inside hy).1
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

theorem exists_source_bounded_side [DiscreteTopology L]
    (he : PLDomain e R) (hsource : D1 ×ˢ (univ : Set V2) ⊆ h.source)
    (s : ChartwisePLSphere e (sphereSet L T)) :
    ∃ U : Set E, IsOpen U ∧ Bornology.IsBounded U ∧
      frontier U = sourceSphere L T ∧ frontier (closure U) = sourceSphere L T := by
  let a : E ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨b, hb, _⟩ := s.exists_finitePL_chart_image he.compatible retained.index
    (sphereSet_subset_chart L T retained)
  obtain ⟨flat⟩ := nonempty_locallyFlat_finitePL_sphere b hb
  have htarget : (e retained.index) '' sphereSet L T ⊆ h.target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := sphereSet_subset_block L T hz
    rw [retained.formula x hx]
    exact h.mapsTo (hsource ⟨hx.1, mem_univ _⟩)
  obtain ⟨sourceFlat⟩ := flat.nonempty_inverse_chart_image h a htarget
  change LocallyFlatTopologicalSphere
    (a '' (h.symm '' ((e retained.index) '' sphereSet L T))) at sourceFlat
  rw [sourceSphere_image_eq L T retained hsource] at sourceFlat
  obtain ⟨U, _, hU, _, _, _, _, _, hfront, _, _, _, hcompact, hclosure, _⟩ :=
    sourceFlat.exists_bounded_complement_components
  have hcompact' : IsCompact (closure (a ⁻¹' U)) := by
    change IsCompact (closure (a.toHomeomorph ⁻¹' U))
    rw [← a.toHomeomorph.preimage_closure]
    exact a.toHomeomorph.isCompact_preimage.mpr hcompact
  refine ⟨a ⁻¹' U, hU.preimage a.continuous,
    hcompact'.isBounded.subset subset_closure, ?_, ?_⟩
  · change frontier (a.toHomeomorph ⁻¹' U) = sourceSphere L T
    rw [← a.toHomeomorph.preimage_frontier, hfront]
    exact preimage_image_eq _ a.injective
  · change frontier (closure (a.toHomeomorph ⁻¹' U)) = sourceSphere L T
    rw [← a.toHomeomorph.preimage_closure, ← a.toHomeomorph.preimage_frontier, hclosure]
    exact preimage_image_eq _ a.injective

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
