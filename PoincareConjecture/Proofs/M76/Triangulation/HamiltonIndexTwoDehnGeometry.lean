import PoincareConjecture.Proofs.M76.Triangulation.HamiltonDehnRegionLift
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoCoverCoordinates











set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76

open HamiltonIndexTwoStandard

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => ((Fin 2 ⊕ Fin 1) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 1)

private theorem dehn_square_closed (x : V2) :
    (x 0, x 1) ∈ base 1 ↔ x ∈ closedBall (0 : V2) 1 := by
  rw [mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  constructor
  · intro hx i
    fin_cases i
    · rw [Real.norm_eq_abs]
      exact abs_le.mpr hx.1
    · rw [Real.norm_eq_abs]
      exact abs_le.mpr hx.2
  · intro hx
    exact ⟨abs_le.mp (by simpa only [Real.norm_eq_abs] using hx 0),
      abs_le.mp (by simpa only [Real.norm_eq_abs] using hx 1)⟩

private theorem dehn_square_boundary (x : V2) :
    (x 0, x 1) ∈ baseBoundary 1 ↔ x ∈ sphere (0 : V2) 1 := by
  let a := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph
  have hbase : a ⁻¹' base 1 = closedBall (0 : V2) 1 := by
    ext y
    exact dehn_square_closed y
  have hfront : frontier (base 1) = baseBoundary 1 :=
    (base_ballPair (by norm_num : (0 : ℝ) < 1)).frontier_eq_of_finrank_eq rfl
  have heq := a.preimage_frontier (base 1)
  rw [hfront, hbase, frontier_closedBall _ one_ne_zero] at heq
  change x ∈ a ⁻¹' baseBoundary 1 ↔ x ∈ sphere (0 : V2) 1
  rw [heq]

private theorem dehn_free_closed (x : V1) {r : ℝ} (hr : 0 ≤ r) :
    x 0 ∈ Icc (-r) r ↔ x ∈ closedBall (0 : V1) r := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  constructor
  · intro hx i
    fin_cases i
    rw [Real.norm_eq_abs]
    exact abs_le.mpr hx
  · intro hx
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hx 0)

private theorem dehn_cover_image (x : W) (S : Set ((ℝ × ℝ) × ℝ)) :
    coverCoordinates x ∈ coordinates '' S ↔
      ((x (Sum.inl 0), x (Sum.inl 1)), x (Sum.inr 0)) ∈ S := by
  constructor
  · rintro ⟨z, hz, heq⟩
    have hz' : z = ((x (Sum.inl 0), x (Sum.inl 1)), x (Sum.inr 0)) :=
      coordinates.injective heq
    exact hz' ▸ hz
  · intro hx
    exact ⟨_, hx, rfl⟩

private theorem dehn_cover_box (x : W) :
    coverCoordinates x ∈ Icc lowerBound upperBound ↔
      (fun i => x (Sum.inl i)) ∈ closedBall (0 : V2) 1 ∧
      (fun i => x (Sum.inr i)) ∈ closedBall (0 : V1) 2 := by
  rw [← box_image, dehn_cover_image]
  exact and_congr (dehn_square_closed (fun i => x (Sum.inl i)))
    (dehn_free_closed (fun i => x (Sum.inr i)) (r := 2) (by norm_num))

private theorem dehn_cover_side (x : W) :
    coverCoordinates x ∈ side ↔
      (fun i => x (Sum.inl i)) ∈ sphere (0 : V2) 1 ∧
      (fun i => x (Sum.inr i)) ∈ closedBall (0 : V1) (3 / 2) := by
  rw [side, dehn_cover_image]
  exact and_congr (dehn_square_boundary (fun i => x (Sum.inl i)))
    (dehn_free_closed (fun i => x (Sum.inr i)) (r := 3 / 2) (by norm_num))

private theorem dehn_cover_frontier {x : W}
    (hx : coverCoordinates x ∈ frontier (Icc lowerBound upperBound))
    (ht : |x (Sum.inr 0)| < 2) :
    (fun i => x (Sum.inl i)) ∈ sphere (0 : V2) 1 := by
  change coverCoordinates x ∈ frontier (Icc frame.lower frame.upper) at hx
  rw [frame.frontier_eq] at hx
  rcases hx with (hx | hx) | hx
  · exact ((dehn_cover_side x).mp hx).1
  · change coverCoordinates x ∈ coordinates '' lowerOuter (-2) (-(3 / 2)) at hx
    rw [dehn_cover_image] at hx
    rcases hx with hx | hx
    · exact (dehn_square_boundary _).mp hx.1
    · have hh : x (Sum.inr 0) = -2 := hx.2
      rw [hh] at ht
      norm_num at ht
  · change coverCoordinates x ∈ coordinates '' upperOuter (3 / 2) 2 at hx
    rw [dehn_cover_image] at hx
    rcases hx with hx | hx
    · exact (dehn_square_boundary _).mp hx.1
    · have hh : x (Sum.inr 0) = 2 := hx.2
      rw [hh] at ht
      norm_num at ht

variable (L : Submodule ℤ V1) {α : Type*}
  (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3)
  (T : HamiltonProtectedDehnDisks L e)
  (region : HamiltonDehnEnclosingRegion (Fin 2) (Fin 1) L e (⋃ b, T.surface b))





structure HamiltonIndexTwoDehnGeometry where
  Psum : Set W
  deltaSum : Bool → Set W
  Psum_eq : Psum = {y | (fun i => y (Sum.inl i)) ∈ closedBall (0 : V2) 1 ∧
    (fun i => y (Sum.inr i)) ∈ closedBall (0 : V1) 2} ∩
      (latticeCoordinateProjection (Fin 2) (Fin 1) L) ⁻¹' region.region
  deltaSum_eq : ∀ b, deltaSum b =
    {y | (fun i => y (Sum.inl i)) ∈ closedBall (0 : V2) 1 ∧
      (fun i => y (Sum.inr i)) ∈ closedBall (0 : V1) 2} ∩
        (latticeCoordinateProjection (Fin 2) (Fin 1) L) ⁻¹' T.surface b
  radius : ℝ
  radius_gt_one : 1 < radius
  radius_lt_two : radius < 2
  compact : IsCompact Psum
  disk_compact : ∀ b, IsCompact (deltaSum b)
  in_cylinder : Psum ⊆ coordinateCylinder J
  norm_le : ∀ y ∈ Psum, ‖y‖ ≤ radius
  regionProjection : Psum ≃ₜ region.region
  regionProjection_eq : ∀ y : Psum,
    (regionProjection y : LatticeHandleAmbient (Fin 2) (Fin 1) L) =
      latticeCoordinateProjection (Fin 2) (Fin 1) L y
  diskProjection : ∀ b, deltaSum b ≃ₜ T.surface b
  diskProjection_eq : ∀ b (y : deltaSum b),
    (diskProjection b y : LatticeHandleAmbient (Fin 2) (Fin 1) L) =
      latticeCoordinateProjection (Fin 2) (Fin 1) L y
  diskParameter : ∀ b, closedBall (0 : V2) 1 ≃ₜ deltaSum b
  diskParameter_projection : ∀ b (x : closedBall (0 : V2) 1),
    T.map b x = latticeCoordinateProjection (Fin 2) (Fin 1) L (diskParameter b x)
  diskParameter_boundary : ∀ b (x : closedBall (0 : V2) 1),
    (x : V2) ∈ sphere (0 : V2) 1 →
      coverCoordinates (diskParameter b x) = ![x.val 0, x.val 1, endHeight b]
  subset_box : coverCoordinates '' Psum ⊆ Icc lowerBound upperBound
  boundary_contact : (coverCoordinates '' Psum) ∩
    frontier (Icc lowerBound upperBound) = side
  disk_subset : ∀ b, deltaSum b ⊆ Psum
  disk_side : ∀ b, (coverCoordinates '' deltaSum b) ∩ side = rim b
  disks_disjoint : Disjoint (deltaSum false) (deltaSum true)
  sphere_iff : ∀ y ∈ Psum,
    latticeCoordinateProjection (Fin 2) (Fin 1) L y ∈ frontier region.region ↔
      coverCoordinates y ∈
        (side ∪ coverCoordinates '' deltaSum false) ∪ coverCoordinates '' deltaSum true





theorem HamiltonRetainedBlockChart.exists_indexTwo_dehn_geometry
    [DiscreteTopology L] {h : OpenPartialHomeomorph (V2 × V1) V3}
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    Nonempty (HamiltonIndexTwoDehnGeometry L e T region) := by
  classical
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 1)
    (fun _ => ℝ)).toHomeomorph
  let C2 : Set (V2 × V1) := closedBall (0 : V2) 1 ×ˢ closedBall (0 : V1) 2
  let pi := latticeCoordinateProjection (Fin 2) (Fin 1) L
  let pull (B : Set (V2 × V1)) : (c ⁻¹' B) ≃ₜ B :=
    (c.image (c ⁻¹' B)).trans (Homeomorph.setCongr (c.image_preimage B))
  obtain ⟨P, r, hPeq, hP, hr1, hr2, hPr, q, hq⟩ :=
    retained.exists_lifted_enclosing_region region
  have hTcompact (b : Bool) : IsCompact (T.surface b) := by
    let : CompactSpace (closedBall (0 : V2) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact isCompact_iff_compactSpace.mpr (T.parametrization b).compactSpace
  have hdLift (b : Bool) := retained.exists_lifted_compact_subset
    (T.surface b) (hTcompact b) (fun _ hx => (T.inside b hx).1)
  choose delta hdeltaeq hdcompact qd hqd using hdLift
  let Psum : Set W := c ⁻¹' P
  let ds (b : Bool) : Set W := c ⁻¹' delta b
  let qs : Psum ≃ₜ region.region := (pull P).trans q
  let qds (b : Bool) : ds b ≃ₜ T.surface b := (pull (delta b)).trans (qd b)
  let dp (b : Bool) : closedBall (0 : V2) 1 ≃ₜ ds b :=
    (T.parametrization b).trans (qds b).symm
  have hPmem (x : W) : x ∈ Psum ↔ c x ∈ C2 ∧ pi x ∈ region.region := by
    change c x ∈ P ↔ _
    rw [hPeq]
    rfl
  have hdmem (b : Bool) (x : W) : x ∈ ds b ↔ c x ∈ C2 ∧ pi x ∈ T.surface b := by
    change c x ∈ delta b ↔ _
    rw [hdeltaeq b]
    rfl
  have hqs (x : Psum) :
      (qs x : LatticeHandleAmbient (Fin 2) (Fin 1) L) = pi x := by
    exact hq ⟨c x, x.property⟩
  have hqds (b : Bool) (x : ds b) :
      (qds b x : LatticeHandleAmbient (Fin 2) (Fin 1) L) = pi x := by
    exact hqd b ⟨c x, x.property⟩
  have hdproj (b : Bool) (x : closedBall (0 : V2) 1) :
      T.map b x = pi (dp b x) := by
    rw [T.map_eq]
    have heq : qds b (dp b x) = T.parametrization b x :=
      (qds b).apply_symm_apply (T.parametrization b x)
    rw [← heq, hqds]
  have hTP (b : Bool) : T.surface b ⊆ region.region := by
    intro x hx
    apply region.compact.isClosed.frontier_subset
    rw [region.frontier_eq]
    exact Or.inl (mem_iUnion.mpr ⟨b, hx⟩)
  have hdP (b : Bool) : ds b ⊆ Psum := by
    intro x hx
    have hm := (hdmem b x).mp hx
    exact (hPmem x).mpr ⟨hm.1, hTP b hm.2⟩
  have hPC (x : W) (hx : x ∈ Psum) : c x ∈ C2 := ((hPmem x).mp hx).1
  have hPfree (x : W) (hx : x ∈ Psum) :
      (c x).2 ∈ ball (0 : V1) r := (hPr hx).2
  have hPiBoundary (x : W) :
      pi x ∈ frontier (latticeHandleDomain (Fin 2) (Fin 1) L) ↔
        (c x).1 ∈ sphere (0 : V2) 1 := by
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact and_iff_left (mem_univ _)
  have hAtt (x : W) (hx : c x ∈ C2) :
      pi x ∈ hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2) ↔
        coverCoordinates x ∈ side := by
    constructor
    · rintro ⟨z, hz, hzpi⟩
      have hzC : z ∈ C2 := ⟨sphere_subset_closedBall hz.1,
        closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hz.2⟩
      have heq : z = c x := retained.quotient_injective hzC hx hzpi
      apply (dehn_cover_side x).mpr
      change (c x).1 ∈ sphere (0 : V2) 1 ∧
        (c x).2 ∈ closedBall (0 : V1) (3 / 2)
      rw [← heq]
      exact hz
    · intro hs
      exact ⟨c x, (dehn_cover_side x).mp hs, rfl⟩
  have hdBoundary (b : Bool) (x : closedBall (0 : V2) 1)
      (hx : (x : V2) ∈ sphere (0 : V2) 1) :
      coverCoordinates (dp b x) = ![x.val 0, x.val 1, endHeight b] := by
    let z : V2 × V1 := (x, fun _ => endHeight b)
    have hzC : z ∈ C2 := by
      refine ⟨x.property, ?_⟩
      apply (dehn_free_closed _ (by norm_num : (0 : ℝ) ≤ 2)).mp
      cases b <;> norm_num [z, endHeight]
    have heq : c (dp b x) = z := retained.quotient_injective
      (hPC _ (hdP b (dp b x).property)) hzC
        ((hdproj b x).symm.trans (T.boundary_values b x hx))
    exact congrArg (fun z : V2 × V1 => ![z.1 0, z.1 1, z.2 0]) heq
  have hnorm (x : W) (hx : x ∈ Psum) : ‖x‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num) hr1.le)).mpr
    intro i
    rcases i with i | i
    · exact (norm_le_pi_norm (c x).1 i).trans
        ((mem_closedBall_zero_iff.mp (hPC x hx).1).trans hr1.le)
    · exact (norm_le_pi_norm (c x).2 i).trans
        (mem_ball_zero_iff.mp (hPfree x hx)).le
  have hbox : coverCoordinates '' Psum ⊆ Icc lowerBound upperBound := by
    rintro _ ⟨x, hx, rfl⟩
    exact (dehn_cover_box x).mpr (hPC x hx)
  have hsideFront : side ⊆ frontier (Icc lowerBound upperBound) := by
    intro x hx
    exact frame.frontier_eq.symm.subset (Or.inl (Or.inl hx))
  have hcontact : (coverCoordinates '' Psum) ∩
      frontier (Icc lowerBound upperBound) = side := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hfront⟩
      have ht : |x (Sum.inr 0)| < 2 := by
        have ht' := (norm_le_pi_norm (c x).2 0).trans_lt
          ((mem_ball_zero_iff.mp (hPfree x hx)).trans hr2)
        change ‖x (Sum.inr 0)‖ < 2 at ht'
        rw [Real.norm_eq_abs] at ht'
        exact ht'
      have hb : pi x ∈ frontier (latticeHandleDomain (Fin 2) (Fin 1) L) :=
        (hPiBoundary x).mpr (dehn_cover_frontier hfront ht)
      exact (hAtt x (hPC x hx)).mp
        (region.old_boundary_eq.subset ⟨((hPmem x).mp hx).2, hb⟩)
    · intro y hy
      let x : W := coverCoordinates.symm y
      have hxy : coverCoordinates x = y := coverCoordinates.apply_symm_apply y
      have hs : coverCoordinates x ∈ side := hxy.symm ▸ hy
      have hc : c x ∈ C2 := by
        have hv := (dehn_cover_side x).mp hs
        exact ⟨sphere_subset_closedBall hv.1,
          closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hv.2⟩
      have hp : pi x ∈ region.region :=
        (region.old_boundary_eq.symm.subset ((hAtt x hc).mpr hs)).1
      exact ⟨⟨x, (hPmem x).mpr ⟨hc, hp⟩, hxy⟩, hsideFront hy⟩
  have hdside (b : Bool) : (coverCoordinates '' ds b) ∩ side = rim b := by
    apply Subset.antisymm
    · rintro _ ⟨⟨y, hy, rfl⟩, hs⟩
      let x := (dp b).symm ⟨y, hy⟩
      have hxy : (dp b x : W) = y :=
        congrArg Subtype.val ((dp b).apply_symm_apply ⟨y, hy⟩)
      have hval : (T.parametrization b x : LatticeHandleAmbient (Fin 2) (Fin 1) L) =
          pi y := by
        rw [← T.map_eq, hdproj, hxy]
      have hxs : (x : V2) ∈ sphere (0 : V2) 1 := by
        apply (T.old_boundary_iff b x).mp
        rw [hval]
        exact (hPiBoundary y).mpr ((dehn_cover_side y).mp hs).1
      have hb := hdBoundary b x hxs
      rw [hxy] at hb
      rw [hb]
      exact ⟨((x.val 0, x.val 1), endHeight b),
        ⟨(dehn_square_boundary x).mpr hxs, rfl⟩, rfl⟩
    · intro y hy
      have hs : y ∈ side := ((source.disk_side b).symm.subset hy).2
      obtain ⟨z, hz, rfl⟩ := hy
      let u : V2 := ![z.1.1, z.1.2]
      have hu : u ∈ sphere (0 : V2) 1 := (dehn_square_boundary u).mp hz.1
      let ub : closedBall (0 : V2) 1 := ⟨u, sphere_subset_closedBall hu⟩
      have heq : coverCoordinates (dp b ub) = coordinates z := by
        rw [hdBoundary b ub hu]
        ext i
        fin_cases i
        · rfl
        · rfl
        · exact hz.2.symm
      exact ⟨⟨dp b ub, (dp b ub).property, heq⟩, hs⟩
  have hdis : Disjoint (ds false) (ds true) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp T.disjoint ((hdmem false x).mp hx).2
      ((hdmem true x).mp hy).2
  have hsphere (x : W) (hx : x ∈ Psum) :
      pi x ∈ frontier region.region ↔ coverCoordinates x ∈
        (side ∪ coverCoordinates '' ds false) ∪ coverCoordinates '' ds true := by
    rw [region.frontier_eq]
    constructor
    · rintro (hd | ha)
      · obtain ⟨b, hb⟩ := mem_iUnion.mp hd
        have hb' : coverCoordinates x ∈ coverCoordinates '' ds b :=
          mem_image_of_mem coverCoordinates ((hdmem b x).mpr ⟨hPC x hx, hb⟩)
        cases b with
        | false => exact Or.inl (Or.inr hb')
        | true => exact Or.inr hb'
      · exact Or.inl (Or.inl ((hAtt x (hPC x hx)).mp ha))
    · rintro ((hs | hf) | ht)
      · exact Or.inr ((hAtt x (hPC x hx)).mpr hs)
      · obtain ⟨y, hy, heq⟩ := hf
        have hyx : y = x := coverCoordinates.injective heq
        exact Or.inl (mem_iUnion.mpr ⟨false, ((hdmem false x).mp (hyx ▸ hy)).2⟩)
      · obtain ⟨y, hy, heq⟩ := ht
        have hyx : y = x := coverCoordinates.injective heq
        exact Or.inl (mem_iUnion.mpr ⟨true, ((hdmem true x).mp (hyx ▸ hy)).2⟩)
  refine ⟨{
    Psum := Psum
    deltaSum := ds
    Psum_eq := Set.ext hPmem
    deltaSum_eq := fun b => Set.ext (hdmem b)
    radius := r
    radius_gt_one := hr1
    radius_lt_two := hr2
    compact := c.isCompact_preimage.mpr hP
    disk_compact := fun b => c.isCompact_preimage.mpr (hdcompact b)
    in_cylinder := ?_
    norm_le := hnorm
    regionProjection := qs
    regionProjection_eq := hqs
    diskProjection := qds
    diskProjection_eq := hqds
    diskParameter := dp
    diskParameter_projection := hdproj
    diskParameter_boundary := hdBoundary
    subset_box := hbox
    boundary_contact := hcontact
    disk_subset := hdP
    disk_side := hdside
    disks_disjoint := hdis
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
