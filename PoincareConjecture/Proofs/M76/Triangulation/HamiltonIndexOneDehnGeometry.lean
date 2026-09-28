import PoincareConjecture.Proofs.M76.Triangulation.HamiltonDehnRegionLift
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerHandleCorrection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCoverCoordinates









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open HamiltonIndexOne

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 1 ↪ Fin 1 ⊕ Fin 2)

private theorem dehn_interval_closed (x : V1) :
    x 0 ∈ Icc (-1 : ℝ) 1 ↔ x ∈ closedBall (0 : V1) 1 := by
  rw [mem_closedBall_zero_iff, ← boundedCoordinate_norm, Real.norm_eq_abs]
  exact abs_le.symm

private theorem dehn_interval_boundary (x : V1) :
    x 0 ∈ ({-1, 1} : Set ℝ) ↔ x ∈ sphere (0 : V1) 1 := by
  rw [mem_sphere_zero_iff_norm, ← boundedCoordinate_norm, Real.norm_eq_abs]
  simp only [mem_insert_iff, mem_singleton_iff, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  exact or_comm

private theorem dehn_cover_block (x : V) :
    coverCoordinates x ∈ squareBlock ↔
      (fun i => x (Sum.inl i)) ∈ closedBall (0 : V1) 1 ∧
      (fun i => x (Sum.inr i)) ∈ closedBall (0 : V2) 2 := by
  change (x (Sum.inl 0) ∈ Icc (-1 : ℝ) 1 ∧
    (x (Sum.inr 0), x (Sum.inr 1)) ∈ closedBall (0 : ℝ × ℝ) 2) ↔ _
  rw [dehn_interval_closed (fun i => x (Sum.inl i))]
  simp only [mem_closedBall_zero_iff, freeCoordinates_norm (fun i => x (Sum.inr i))]

private theorem dehn_cover_attaching (x : V) :
    coverCoordinates x ∈ squareAttachingDisks ↔
      (fun i => x (Sum.inl i)) ∈ sphere (0 : V1) 1 ∧
      (fun i => x (Sum.inr i)) ∈ closedBall (0 : V2) (3 / 2) := by
  change (x (Sum.inl 0) ∈ ({-1, 1} : Set ℝ) ∧
    (x (Sum.inr 0), x (Sum.inr 1)) ∈ closedBall (0 : ℝ × ℝ) (3 / 2)) ↔ _
  rw [dehn_interval_boundary (fun i => x (Sum.inl i))]
  simp only [mem_closedBall_zero_iff, freeCoordinates_norm (fun i => x (Sum.inr i))]

private theorem dehn_attaching_frontier : squareAttachingDisks ⊆ frontier squareBlock := by
  intro x hx
  have hs : x.1 = -1 ∨ x.1 = 1 := by
    simpa only [mem_insert_iff, mem_singleton_iff] using hx.1
  have hi : x.1 ∈ Icc (-1 : ℝ) 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  refine ⟨subset_closure ⟨hi,
    closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hx.2⟩, ?_⟩
  intro hxi
  rw [squareBlock, interior_prod_eq, interior_Icc] at hxi
  rcases hs with hs | hs
  · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hxi.1.1)
  · exact (lt_irrefl (1 : ℝ)) (hs ▸ hxi.1.2)

variable (L : Submodule ℤ V2) {α : Type*}
  (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3)
  (T : HamiltonProtectedDehnAnnulus L e)
  (region : HamiltonDehnEnclosingRegion (Fin 1) (Fin 2) L e T.surface)




structure HamiltonIndexOneDehnGeometry where
  Psum : Set V
  annulusSum : Set V
  Psum_eq : Psum = {y | (fun i => y (Sum.inl i)) ∈ closedBall (0 : V1) 1 ∧
    (fun i => y (Sum.inr i)) ∈ closedBall (0 : V2) 2} ∩
      (latticeCoordinateProjection (Fin 1) (Fin 2) L) ⁻¹' region.region
  annulusSum_eq : annulusSum =
    {y | (fun i => y (Sum.inl i)) ∈ closedBall (0 : V1) 1 ∧
      (fun i => y (Sum.inr i)) ∈ closedBall (0 : V2) 2} ∩
        (latticeCoordinateProjection (Fin 1) (Fin 2) L) ⁻¹' T.surface
  radius : ℝ
  radius_gt_one : 1 < radius
  radius_lt_two : radius < 2
  compact : IsCompact Psum
  annulus_compact : IsCompact annulusSum
  in_cylinder : Psum ⊆ coordinateCylinder J
  norm_le : ∀ y ∈ Psum, ‖y‖ ≤ radius
  regionProjection : Psum ≃ₜ region.region
  regionProjection_eq : ∀ y : Psum,
    (regionProjection y : LatticeHandleAmbient (Fin 1) (Fin 2) L) =
      latticeCoordinateProjection (Fin 1) (Fin 2) L y
  annulusProjection : annulusSum ≃ₜ T.surface
  annulusProjection_eq : ∀ y : annulusSum,
    (annulusProjection y : LatticeHandleAmbient (Fin 1) (Fin 2) L) =
      latticeCoordinateProjection (Fin 1) (Fin 2) L y
  annulusParameter : annulusParameterSpace ≃ₜ annulusSum
  annulusParameter_projection : ∀ x : annulusParameterSpace,
    T.map x = latticeCoordinateProjection (Fin 1) (Fin 2) L (annulusParameter x)
  annulusParameter_boundary : ∀ x : annulusParameterSpace,
    (x : V1 × V2).1 ∈ sphere (0 : V1) 1 →
      coverCoordinates (annulusParameter x) = annulusCoordinates x
  subset_box : coverCoordinates '' Psum ⊆ squareBlock
  boundary_contact : (coverCoordinates '' Psum) ∩ frontier squareBlock = squareAttachingDisks
  annulus_subset : annulusSum ⊆ Psum
  annulus_contact : (coverCoordinates '' annulusSum) ∩ frontier squareBlock = squareRims
  core_subset : closedBall (0 : V) 1 ⊆ Psum
  core_disjoint : Disjoint (closedBall (0 : V) 1) annulusSum
  sphere_iff : ∀ y ∈ Psum,
    latticeCoordinateProjection (Fin 1) (Fin 2) L y ∈ frontier region.region ↔
      coverCoordinates y ∈ (coverCoordinates '' annulusSum) ∪ squareAttachingDisks




theorem HamiltonRetainedBlockChart.exists_indexOne_dehn_geometry
    [DiscreteTopology L] {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) :
    Nonempty (HamiltonIndexOneDehnGeometry L e T region) := by
  classical
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
    (fun _ => ℝ)).toHomeomorph
  let C2 : Set (V1 × V2) := closedBall (0 : V1) 1 ×ˢ closedBall (0 : V2) 2
  let pi := latticeCoordinateProjection (Fin 1) (Fin 2) L
  let pull (B : Set (V1 × V2)) : (c ⁻¹' B) ≃ₜ B :=
    (c.image (c ⁻¹' B)).trans (Homeomorph.setCongr (c.image_preimage B))
  obtain ⟨P, r, hPeq, hP, hr1, hr2, hPr, q, hq⟩ :=
    retained.exists_lifted_enclosing_region region
  have hTcompact : IsCompact T.surface := by
    let : CompactSpace (closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1) :=
      isCompact_iff_compactSpace.mp
      ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
    exact isCompact_iff_compactSpace.mpr T.parametrization.compactSpace
  obtain ⟨Z, hZeq, hZ, qZ, hqZ⟩ := retained.exists_lifted_compact_subset
    T.surface hTcompact (fun _ hx => (T.inside hx).1)
  let Psum : Set V := c ⁻¹' P
  let Zsum : Set V := c ⁻¹' Z
  let qs : Psum ≃ₜ region.region := (pull P).trans q
  let qzs : Zsum ≃ₜ T.surface := (pull Z).trans qZ
  let u : annulusParameterSpace ≃ₜ Zsum := T.parametrization.trans qzs.symm
  have hPmem (x : V) : x ∈ Psum ↔ c x ∈ C2 ∧ pi x ∈ region.region := by
    change c x ∈ P ↔ _
    rw [hPeq]
    rfl
  have hZmem (x : V) : x ∈ Zsum ↔ c x ∈ C2 ∧ pi x ∈ T.surface := by
    change c x ∈ Z ↔ _
    rw [hZeq]
    rfl
  have hqs (x : Psum) :
      (qs x : LatticeHandleAmbient (Fin 1) (Fin 2) L) = pi x := hq ⟨c x, x.property⟩
  have hqzs (x : Zsum) :
      (qzs x : LatticeHandleAmbient (Fin 1) (Fin 2) L) = pi x := hqZ ⟨c x, x.property⟩
  have huproj (x : annulusParameterSpace) : T.map x = pi (u x) := by
    have heq : qzs (u x) = T.parametrization x := qzs.apply_symm_apply (T.parametrization x)
    calc
      T.map x = (T.parametrization x : LatticeHandleAmbient (Fin 1) (Fin 2) L) := T.map_eq x
      _ = (qzs (u x) : LatticeHandleAmbient (Fin 1) (Fin 2) L) := congrArg Subtype.val heq.symm
      _ = pi (u x) := hqzs (u x)
  have hTP : T.surface ⊆ region.region := by
    intro x hx
    exact region.compact.isClosed.frontier_subset
      (region.frontier_eq.symm.subset (Or.inl hx))
  have hZP : Zsum ⊆ Psum := fun x hx =>
    (hPmem x).mpr ⟨((hZmem x).mp hx).1, hTP ((hZmem x).mp hx).2⟩
  have hPC (x : V) (hx : x ∈ Psum) : c x ∈ C2 := ((hPmem x).mp hx).1
  have hPfree (x : V) (hx : x ∈ Psum) :
      (c x).2 ∈ ball (0 : V2) r := (hPr hx).2
  have hPiBoundary (x : V) :
      pi x ∈ frontier (latticeHandleDomain (Fin 1) (Fin 2) L) ↔
        (c x).1 ∈ sphere (0 : V1) 1 := by
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact and_iff_left (mem_univ _)
  have hAtt (x : V) (hx : c x ∈ C2) :
      pi x ∈ hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2) ↔
        coverCoordinates x ∈ squareAttachingDisks := by
    constructor
    · rintro ⟨z, hz, hzpi⟩
      have hzC : z ∈ C2 := ⟨sphere_subset_closedBall hz.1,
        closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hz.2⟩
      have heq : z = c x := retained.quotient_injective hzC hx hzpi
      apply (dehn_cover_attaching x).mpr
      change (c x).1 ∈ sphere (0 : V1) 1 ∧ (c x).2 ∈ closedBall (0 : V2) (3 / 2)
      rwa [← heq]
    · intro hx'
      exact ⟨c x, (dehn_cover_attaching x).mp hx', rfl⟩
  have hnorm (x : V) (hx : x ∈ Psum) : ‖x‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num) hr1.le)).mpr
    intro i
    rcases i with i | i
    · exact (norm_le_pi_norm (c x).1 i).trans
        ((mem_closedBall_zero_iff.mp (hPC x hx).1).trans hr1.le)
    · exact (norm_le_pi_norm (c x).2 i).trans
        (mem_ball_zero_iff.mp (hPfree x hx)).le
  have hfront (x : V) (hx : x ∈ Psum)
      (hxf : coverCoordinates x ∈ frontier squareBlock) :
      (c x).1 ∈ sphere (0 : V1) 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    apply le_antisymm (mem_closedBall_zero_iff.mp (hPC x hx).1)
    by_contra hn
    have hb : ‖(c x).1‖ < 1 := lt_of_not_ge hn
    have hi : x (Sum.inl 0) ∈ Ioo (-1 : ℝ) 1 := by
      apply abs_lt.mp
      change ‖(c x).1 0‖ < 1
      rwa [boundedCoordinate_norm]
    have hf : (x (Sum.inr 0), x (Sum.inr 1)) ∈ ball (0 : ℝ × ℝ) 2 := by
      rw [mem_ball_zero_iff, freeCoordinates_norm (fun i => x (Sum.inr i))]
      exact (mem_ball_zero_iff.mp (hPfree x hx)).trans hr2
    apply hxf.2
    rw [squareBlock, interior_prod_eq, interior_Icc, interior_closedBall _ (by norm_num)]
    exact ⟨hi, hf⟩
  have hcontact : (coverCoordinates '' Psum) ∩ frontier squareBlock = squareAttachingDisks := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxf⟩
      exact (hAtt x (hPC x hx)).mp (region.old_boundary_eq.subset
        ⟨((hPmem x).mp hx).2, (hPiBoundary x).mpr (hfront x hx hxf)⟩)
    · intro y hy
      let x : V := coverCoordinates.symm y
      have hxy : coverCoordinates x = y := coverCoordinates.apply_symm_apply y
      have hs : coverCoordinates x ∈ squareAttachingDisks := hxy.symm ▸ hy
      have hc : c x ∈ C2 := by
        have hv := (dehn_cover_attaching x).mp hs
        exact ⟨sphere_subset_closedBall hv.1,
          closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hv.2⟩
      have hp : pi x ∈ region.region :=
        (region.old_boundary_eq.symm.subset ((hAtt x hc).mpr hs)).1
      exact ⟨⟨x, (hPmem x).mpr ⟨hc, hp⟩, hxy⟩, dehn_attaching_frontier hy⟩
  have hubound (x : annulusParameterSpace) (hx : x.val.1 ∈ sphere (0 : V1) 1) :
      coverCoordinates (u x) = annulusCoordinates x := by
    let z : V1 × V2 := (x.val.1, (3 / 2 : ℝ) • x.val.2)
    have hzC : z ∈ C2 := by
      refine ⟨x.property.1, mem_closedBall_zero_iff.mpr ?_⟩
      change ‖(3 / 2 : ℝ) • x.val.2‖ ≤ 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
        mem_sphere_zero_iff_norm.mp x.property.2]
      norm_num
    have heq : c (u x) = z := retained.quotient_injective
      (hPC _ (hZP (u x).property)) hzC
      ((huproj x).symm.trans (T.boundary_values x ⟨hx, x.property.2⟩))
    exact congrArg productCoordinates heq
  obtain ⟨std, hstd, hstdval⟩ := exists_standard_annulus_parameter
  have hZcontact : (coverCoordinates '' Zsum) ∩ frontier squareBlock = squareRims := by
    apply Subset.antisymm
    · rintro _ ⟨⟨y, hy, rfl⟩, hyf⟩
      let x := u.symm ⟨y, hy⟩
      have hxy : (u x : V) = y := congrArg Subtype.val (u.apply_symm_apply ⟨y, hy⟩)
      have hval : (T.parametrization x : LatticeHandleAmbient (Fin 1) (Fin 2) L) = pi y := by
        exact (T.map_eq x).symm.trans ((huproj x).trans (congrArg pi hxy))
      have hxs : x.val.1 ∈ sphere (0 : V1) 1 := by
        apply (T.old_boundary_iff x).mp
        rw [hval]
        exact (hPiBoundary y).mpr (hfront y (hZP hy) hyf)
      have hb := hubound x hxs
      rw [hxy] at hb
      rw [hb]
      exact (annulusCoordinates_mem_rims x).mpr hxs
    · intro y hy
      have hs : y.1 = -1 ∨ y.1 = 1 := by
        simpa only [mem_insert_iff, mem_singleton_iff] using hy.1
      have hi : y ∈ squareInnerAnnulus := by
        refine ⟨?_, hy.2⟩
        rcases hs with hs | hs <;> rw [hs] <;> norm_num
      let x := std.symm ⟨y, hi⟩
      have hxy : annulusCoordinates x = y :=
        (hstdval x).symm.trans (congrArg Subtype.val (std.apply_symm_apply ⟨y, hi⟩))
      have hxs : x.val.1 ∈ sphere (0 : V1) 1 :=
        (annulusCoordinates_mem_rims x).mp (hxy.symm ▸ hy)
      have hyA : y ∈ squareAttachingDisks := ⟨hy.1, sphere_subset_closedBall hy.2⟩
      exact ⟨⟨u x, (u x).property, (hubound x hxs).trans hxy⟩,
        dehn_attaching_frontier hyA⟩
  have hunit (x : V) (hx : x ∈ closedBall (0 : V) 1) :
      c x ∈ closedBall (0 : V1) 1 ×ˢ closedBall (0 : V2) 1 := by
    have hn := mem_closedBall_zero_iff.mp hx
    constructor <;> apply mem_closedBall_zero_iff.mpr <;>
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    · intro i
      exact (norm_le_pi_norm x (Sum.inl i)).trans hn
    · intro i
      exact (norm_le_pi_norm x (Sum.inr i)).trans hn
  have hcore : closedBall (0 : V) 1 ⊆ Psum := by
    intro x hx
    have hu := hunit x hx
    exact (hPmem x).mpr ⟨⟨hu.1, closedBall_subset_closedBall (by norm_num) hu.2⟩,
      region.core_subset ⟨c x, hu, rfl⟩⟩
  have hdis : Disjoint (closedBall (0 : V) 1) Zsum := by
    apply Set.disjoint_left.mpr
    intro x hx hz
    exact (T.inside ((hZmem x).mp hz).2).2 ⟨c x, hunit x hx, rfl⟩
  have hsphere (x : V) (hx : x ∈ Psum) :
      pi x ∈ frontier region.region ↔
        coverCoordinates x ∈ (coverCoordinates '' Zsum) ∪ squareAttachingDisks := by
    rw [region.frontier_eq]
    constructor
    · rintro (hz | ha)
      · exact Or.inl ⟨x, (hZmem x).mpr ⟨hPC x hx, hz⟩, rfl⟩
      · exact Or.inr ((hAtt x (hPC x hx)).mp ha)
    · rintro (⟨y, hy, heq⟩ | ha)
      · have hyx : y = x := coverCoordinates.injective heq
        exact Or.inl ((hZmem x).mp (hyx ▸ hy)).2
      · exact Or.inr ((hAtt x (hPC x hx)).mpr ha)
  refine ⟨{
    Psum := Psum
    annulusSum := Zsum
    Psum_eq := Set.ext hPmem
    annulusSum_eq := Set.ext hZmem
    radius := r
    radius_gt_one := hr1
    radius_lt_two := hr2
    compact := c.isCompact_preimage.mpr hP
    annulus_compact := c.isCompact_preimage.mpr hZ
    in_cylinder := ?_
    norm_le := hnorm
    regionProjection := qs
    regionProjection_eq := hqs
    annulusProjection := qzs
    annulusProjection_eq := hqzs
    annulusParameter := u
    annulusParameter_projection := huproj
    annulusParameter_boundary := hubound
    subset_box := fun _ hx => by
      obtain ⟨x, hx, rfl⟩ := hx
      exact (dehn_cover_block x).mpr (hPC x hx)
    boundary_contact := hcontact
    annulus_subset := hZP
    annulus_contact := hZcontact
    core_subset := hcore
    core_disjoint := hdis
    sphere_iff := hsphere
  }⟩
  intro x hx i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  have hbound := (norm_le_pi_norm (c x).1 j).trans
    (mem_closedBall_zero_iff.mp (hPC x hx).1)
  change ‖x (Sum.inl j)‖ ≤ 1 at hbound
  rw [Real.norm_eq_abs] at hbound
  exact hbound

end PoincareConjecture.M76
