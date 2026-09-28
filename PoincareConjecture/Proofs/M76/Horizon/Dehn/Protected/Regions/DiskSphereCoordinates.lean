import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Disks.RetainedSlabs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.ChartSphereImage
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.SphereLocalFlatness
import PoincareConjecture.Proofs.M76.Brown.LocallyFlatBoundedRegion

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × V1)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V1) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
  (T : HamiltonProtectedDehnDisks L e)

local notation "pi" => hamiltonMarkedProjection (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L

def sphereSet : Set (LatticeHandleAmbient (Fin 2) (Fin 1) L) :=
  (⋃ b, T.surface b) ∪ hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2)

def sourceSphere : Set E :=
  (D2 ×ˢ closedBall (0 : V1) 2) ∩ pi ⁻¹' sphereSet L T

def sourceProtectedDisks : Set E :=
  (D2 ×ˢ closedBall (0 : V1) 2) ∩ pi ⁻¹' (⋃ b, T.surface b)

theorem sourceProtectedDisks_inside :
    sourceProtectedDisks L T ⊆ (D2 ×ˢ closedBall (0 : V1) 2) \
      (D2 ×ˢ closedBall (0 : V1) 1) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨b, hb⟩ := mem_iUnion.mp hx.2
  exact fun hxcore => (T.inside b hb).2 ⟨x, hxcore, rfl⟩

theorem sphereSet_subset_block : sphereSet L T ⊆ hamiltonHandleBlock (Fin 2) (Fin 1) L 2 := by
  intro y hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact (T.inside b hb).1
  · exact ⟨x, ⟨sphere_subset_closedBall hx.1,
      closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hx.2⟩, rfl⟩

theorem sphereSet_subset_outer_open :
    sphereSet L T ⊆ pi '' (D2 ×ˢ ball (0 : V1) 2) := by
  intro y hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact T.inside_outer_open b hb
  · exact ⟨x, ⟨sphere_subset_closedBall hx.1,
      closedBall_subset_ball (by norm_num : (3 / 2 : ℝ) < 2) hx.2⟩, rfl⟩

theorem sphereSet_old_boundary :
    sphereSet L T ∩ frontier R = hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2) := by
  apply Subset.antisymm
  · intro y hy
    rcases hy.1 with hyT | hyA
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hyT
      let x := (T.parametrization b).symm ⟨y, hb⟩
      have hpx : (T.parametrization b x : LatticeHandleAmbient (Fin 2) (Fin 1) L) = y :=
        congrArg Subtype.val ((T.parametrization b).apply_symm_apply ⟨y, hb⟩)
      have hxQ : (x : V2) ∈ Q2 := (T.old_boundary_iff b x).mp (hpx.symm ▸ hy.2)
      have hyval : y = pi ((x : V2), height b) := by
        rw [← hpx, ← T.map_eq b x]
        exact T.boundary_values b x hxQ
      refine ⟨((x : V2), height b), ⟨hxQ, ?_⟩, hyval.symm⟩
      rw [mem_closedBall_zero_iff]
      change ‖(fun _ : Fin 1 => if b then (3 / 2 : ℝ) else -(3 / 2 : ℝ))‖ ≤ (3 / 2 : ℝ)
      rw [pi_norm_const]
      split_ifs <;> norm_num
    · exact hyA
  · intro y hy
    refine ⟨Or.inr hy, ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hx.1, mem_univ _⟩

variable {h : OpenPartialHomeomorph E V3}
  (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h)

include retained

theorem sourceSphere_outer_open : sourceSphere L T ⊆ D2 ×ˢ ball (0 : V1) 2 := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := sphereSet_subset_outer_open L T hx.2
  have hy2 : y ∈ D2 ×ˢ closedBall (0 : V1) 2 := ⟨hy.1, ball_subset_closedBall hy.2⟩
  exact retained.quotient_injective hy2 hx.1 heq ▸ hy

theorem sourceSphere_old_boundary :
    sourceSphere L T ∩ frontier (D2 ×ˢ (univ : Set V1)) =
      Q2 ×ˢ closedBall (0 : V1) (3 / 2) := by
  apply Subset.antisymm
  · intro x hx
    have hxQ : x.1 ∈ Q2 := by
      simpa only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero,
        mem_prod, mem_univ, and_true] using hx.2
    have hpi : pi x ∈ frontier R := by
      rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
      exact ⟨hxQ, mem_univ _⟩
    obtain ⟨y, hy, heq⟩ := (sphereSet_old_boundary L T).subset ⟨hx.1.2, hpi⟩
    have hy2 : y ∈ D2 ×ˢ closedBall (0 : V1) 2 :=
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
    sourceSphere L T = sourceProtectedDisks L T ∪
      (Q2 ×ˢ closedBall (0 : V1) (3 / 2)) := by
  apply Subset.antisymm
  · intro x hx
    rcases hx.2 with hxK | hxA
    · exact Or.inl ⟨hx.1, hxK⟩
    · obtain ⟨y, hy, heq⟩ := hxA
      have hy2 : y ∈ D2 ×ˢ closedBall (0 : V1) 2 :=
        ⟨sphere_subset_closedBall hy.1,
          closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hy.2⟩
      exact Or.inr (retained.quotient_injective hy2 hx.1 heq ▸ hy)
  · rintro x (hx | hx)
    · exact ⟨hx.1, Or.inl hx.2⟩
    · exact ((sourceSphere_old_boundary L T retained).symm.subset hx).1

theorem sourceProtectedDisks_outer_open :
    sourceProtectedDisks L T ⊆ D2 ×ˢ ball (0 : V1) 2 :=
  fun _ hx => sourceSphere_outer_open L T retained ⟨hx.1, Or.inl hx.2⟩

theorem sourceProtectedDisks_old_boundary :
    sourceProtectedDisks L T ∩ (Q2 ×ˢ (univ : Set V1)) ⊆
      Q2 ×ˢ closedBall (0 : V1) (3 / 2) := by
  intro x hx
  apply (sourceSphere_old_boundary L T retained).subset
  refine ⟨⟨hx.1.1, Or.inl hx.1.2⟩, ?_⟩
  simpa only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] using hx.2

theorem sourceSphere_disjoint_interior_core :
    Disjoint (sourceSphere L T) (interior (D2 ×ˢ closedBall (0 : V1) 1)) := by
  apply disjoint_left.mpr
  intro x hx hxint
  have hxcore := interior_subset hxint
  rcases hx.2 with hdisks | hside
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hdisks
    exact (T.inside b hb).2 ⟨x, hxcore, rfl⟩
  · obtain ⟨y, hy, heq⟩ := hside
    have hy2 : y ∈ D2 ×ˢ closedBall (0 : V1) 2 :=
      ⟨sphere_subset_closedBall hy.1,
        closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hy.2⟩
    have hxQ : x.1 ∈ Q2 := (retained.quotient_injective hy2 hx.1 heq ▸ hy).1
    rw [interior_prod_eq, interior_closedBall _ one_ne_zero,
      interior_closedBall _ one_ne_zero] at hxint
    exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hxQ).ge)
      (mem_ball_zero_iff.mp hxint.1)

theorem sphereSet_subset_chart : sphereSet L T ⊆ (e retained.index).source := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := sphereSet_subset_block L T hy
  exact retained.contains x hx

theorem sourceSphere_image_eq
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) :
    h.symm '' ((e retained.index) '' sphereSet L T) = sourceSphere L T := by
  apply Subset.antisymm
  · rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := sphereSet_subset_block L T hy
    rw [retained.formula z hz, h.left_inv (hsource ⟨hz.1, mem_univ _⟩)]
    exact ⟨hz, hy⟩
  · intro x hx
    refine ⟨(e retained.index) (pi x), ⟨pi x, hx.2, rfl⟩, ?_⟩
    rw [retained.formula x hx.1, h.left_inv (hsource ⟨hx.1.1, mem_univ _⟩)]

theorem sourceProtectedDisks_image_eq
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) :
    h.symm '' ((e retained.index) '' (⋃ b, T.surface b)) = sourceProtectedDisks L T := by
  apply Subset.antisymm
  · rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, rfl⟩ := (T.inside b hb).1
    rw [retained.formula z hz, h.left_inv (hsource ⟨hz.1, mem_univ _⟩)]
    exact ⟨hz, mem_iUnion.mpr ⟨b, hb⟩⟩
  · intro x hx
    refine ⟨(e retained.index) (pi x), ⟨pi x, hx.2, rfl⟩, ?_⟩
    rw [retained.formula x hx.1, h.left_inv (hsource ⟨hx.1.1, mem_univ _⟩)]

theorem sourceProtectedDisks_isCompact
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) :
    IsCompact (sourceProtectedDisks L T) := by
  have hT : IsCompact (⋃ b, T.surface b) := isCompact_iUnion fun b => by
    let : CompactSpace D2 := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
    let : CompactSpace (T.surface b) := (T.parametrization b).compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hs : (⋃ b, T.surface b) ⊆ (e retained.index).source :=
    fun _ hy => sphereSet_subset_chart L T retained (Or.inl hy)
  have ht : (e retained.index) '' (⋃ b, T.surface b) ⊆ h.target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := sphereSet_subset_block L T (Or.inl hz)
    rw [retained.formula x hx]
    exact h.mapsTo (hsource ⟨hx.1, mem_univ _⟩)
  rw [← sourceProtectedDisks_image_eq L T retained hsource]
  exact (hT.image_of_continuousOn ((e retained.index).continuousOn.mono hs)).image_of_continuousOn
    (h.symm.continuousOn.mono ht)

theorem nonempty_locallyFlat_sourceSphere [DiscreteTopology L]
    (he : PLDomain e R)
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)
    (N : Set E) (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) (a : E ≃L[ℝ] V3) :
    Nonempty (LocallyFlatTopologicalSphere (a '' sourceSphere L T)) := by
  obtain ⟨s⟩ := T.nonempty_chartwisePLSphere he h hsource N hboundary hPL retained
  obtain ⟨b, hb, _⟩ := s.exists_finitePL_chart_image he.compatible retained.index
    (sphereSet_subset_chart L T retained)
  obtain ⟨flat⟩ := nonempty_locallyFlat_finitePL_sphere b hb
  have htarget : (e retained.index) '' sphereSet L T ⊆ h.target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := sphereSet_subset_block L T hz
    rw [retained.formula x hx]
    exact h.mapsTo (hsource ⟨hx.1, mem_univ _⟩)
  have hflat := flat.nonempty_inverse_chart_image h a htarget
  change Nonempty (LocallyFlatTopologicalSphere
    (a '' (h.symm '' ((e retained.index) '' sphereSet L T)))) at hflat
  rwa [sourceSphere_image_eq L T retained hsource] at hflat

theorem exists_source_bounded_side [DiscreteTopology L]
    (he : PLDomain e R)
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)
    (N : Set E) (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ U : Set E, IsOpen U ∧ Bornology.IsBounded U ∧
      frontier U = sourceSphere L T ∧ frontier (closure U) = sourceSphere L T := by
  let a : E ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨flat⟩ := nonempty_locallyFlat_sourceSphere L T retained he hsource N hboundary hPL a
  obtain ⟨U, V, hU, hV, hUc, hVc, hdis, hunion, hfront, hfrontV,
    hbounded, hunbounded, hcompact, hclosure, hclass⟩ := flat.exists_bounded_complement_components
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

omit retained in
theorem sourceProtectedDisks_projection :
    pi '' sourceProtectedDisks L T = ⋃ b, T.surface b := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := (T.inside b hb).1
    exact ⟨x, ⟨hx, mem_iUnion.mpr ⟨b, hb⟩⟩, rfl⟩

end PoincareConjecture.M76.Dehn.ProtectedDisks
