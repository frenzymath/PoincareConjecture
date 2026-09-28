import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalInteriorVertexRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondCoordinateRadii
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedEndpointHalfFaceMaps

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_interior_axis_parameter
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space) :
    let Z := (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space
    IsFinitePLBallPair ℝ Z {(s false).centroid ℝ id, (s true).centroid ℝ id} ∧
      ∃ b : Icc (0 : ℝ) 1 ≃ₜ Z, b.IsFinitePL ∧
        (b ⟨0, le_rfl, zero_le_one⟩ : E) = (s false).centroid ℝ id ∧
        (b ⟨1, zero_le_one, le_rfl⟩ : E) = (s true).centroid ℝ id := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let Z := V.space ∩ (M arc).space
  let bZ := {z | z ∈ Z ∧ (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
  let J := fun j => (K.barycentricDualBlock (s j)).space
  let center := fun j => (s j).centroid ℝ id
  obtain ⟨C0, L, theta, hC, hcv, hzero, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hfeet⟩ := exists_original_signed_tube_faces
      hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet v B
      hsource hface haxis hsheets hregion
  change IsFinitePLBallPair ℝ Z bZ at hZ
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hJV (j : Bool) : J j ⊆ V.space :=
    space_subset_of_le (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr (hvs j)))
  have hJlink (j : Bool) : J j ⊆ (V.link v).space := by
    have hstrict : ({(v : E)} : Finset E) ⊂ s j :=
      (Finset.singleton_subset_iff.mpr (hvs j)).ssubset_of_ne (by
        intro he
        have hc := hcard j
        rw [← he] at hc
        simp at hc)
    simpa only [Finset.centroid_singleton, id_eq] using
      space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset hvK hstrict)
  have hCenterJ (j : Bool) : center j ∈ J j := by
    change (s j).centroid ℝ id ∈ J j
    exact (K.barycentricDualBlock (s j)).vertices_subset_space
      (K.faceCentroid_mem_barycentricDualBlock_vertices (hMK arc (hs j)))
  have hCenterA (j : Bool) : center j ∈ (M arc).space := by
    have hm := ((M arc).barycentricDualBlock (s j)).vertices_subset_space
      ((M arc).faceCentroid_mem_barycentricDualBlock_vertices (hs j))
    exact (M arc).barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le ((M arc).barycentricDualBlock_le (s j)) hm)
  have hne : center false ≠ center true := fun he =>
    Set.disjoint_left.mp hdisj (hCenterJ false) (he ▸ hCenterJ true)
  have hboundary : bZ = {center false, center true} := by
    obtain ⟨x, y, hxy, hp⟩ := hZ.exists_boundary_eq_pair
    have hm (j : Bool) : center j ∈ ({x, y} : Set E) := hp.subset
      ⟨⟨hJV j (hCenterJ j), hCenterA j⟩, Or.inl (hJlink j (hCenterJ j))⟩
    rw [hp]
    rcases hm false with h₀ | h₀ <;> rcases hm true with h₁ | h₁
    · exact False.elim (hne (h₀.trans h₁.symm))
    · simp only [h₀, show center true = y from h₁]
    · rw [h₀, show center true = x from h₁, pair_comm]
    · exact False.elim (hne (h₀.trans h₁.symm))
  have hZ' : IsFinitePLBallPair ℝ Z {center false, center true} := by
    rw [hboundary] at hZ
    exact hZ
  exact ⟨hZ', hZ'.exists_unitInterval_chart_with_endpoints hne⟩

open Classical in
theorem exists_original_interior_half_face_maps_of_joint_maps_of_axis_superset
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hvFr : (g v : X) ∉ frontier R)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space)
    (G : ∀ j, signedTubeDiamond ≃ₜ (K.barycentricDualBlock (s j)).space)
    (hG : ∀ j, (G j).IsFinitePL) (eta : Bool → Fin 2 → Bool)
    (hQ : ∀ j eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G j x : E) ∈ signedCoordinateSector (K.barycentricDualBlock (s j)).space
          (fun i z => B (g z) i.castSucc) (eta j) eps delta)
    (hcenter : ∀ j, (G j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) =
        (s j).centroid ℝ id)
    {Aaxis : Set E} (bArc : Icc (0 : ℝ) 1 ≃ₜ Aaxis) (hbArc : bArc.IsFinitePL)
    (hZAaxis : (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space ⊆ Aaxis) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let Z := V.space ∩ (M arc).space
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let outer := fun i sign => {z | z ∈ face i sign ∧
      (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1)
      (axis : Icc (α : ℝ) (β : ℝ) ≃ₜ Z) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      axis.IsFinitePL ∧
      (∀ t, (axis t : E) = bArc ⟨t, hsub t.property⟩) ∧
      (∀ j, (axis ⟨if j then (β : ℝ) else (α : ℝ),
        by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
          (s (index j)).centroid ℝ id) ∧
      ∀ i sign, ∃ map : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign,
        map.IsFinitePL ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (map ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            bArc ⟨t, hsub t.property⟩) ∧
        (∀ j (x : signedTubeRadius i sign),
          (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
              aligned (index j) ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : P2 × ℝ) ∈ signedTubePrismAxis α β ↔ (map x : E) ∈ Z) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : P2 × ℝ) ∈ signedTubePrismOuter i sign α β ↔ (map x : E) ∈ outer i sign) := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let Z := V.space ∩ (M arc).space
  let bZ := {z | z ∈ Z ∧ (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
  let J := fun j => (K.barycentricDualBlock (s j)).space
  let center := fun j => (s j).centroid ℝ id
  let c := fun (i : Fin 2) z => B (g z) i.castSucc
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let outer := fun i sign => {z | z ∈ face i sign ∧
    (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
  let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
  let rad := fun j i sign => signedCoordinateFace (J j) c (fun _ => true) i sign
  let corner := fun j i sign => (aligned j ⟨signedTubeCorner i sign,
    signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E)
  obtain ⟨C0, L, theta, hC, hcv, hzero, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hfeet⟩ := exists_original_signed_tube_faces
      hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet v B
      hsource hface haxis hsheets hregion
  change IsFinitePLBallPair ℝ Z bZ at hZ
  obtain ⟨hD, hmiss, hinside⟩ := original_interior_vertex_region_eq hAC hAR K H g hg hgPL
    M hMK reg fr arc hreg hfr harc v B hsource hface hvFr
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
    obtain ⟨u, hu, htu⟩ := K.exists_original_star_face_of_vertex_dual_face hvK ht
    exact hsource ((K.closedStar v).convexHull_subset_space hu (htu hzt))
  have hJV (j : Bool) : J j ⊆ V.space :=
    space_subset_of_le (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr (hvs j)))
  have hJlink (j : Bool) : J j ⊆ (V.link v).space := by
    have hstrict : ({(v : E)} : Finset E) ⊂ s j :=
      (Finset.singleton_subset_iff.mpr (hvs j)).ssubset_of_ne (by
        intro he
        have hc := hcard j
        rw [← he] at hc
        simp at hc)
    simpa only [Finset.centroid_singleton, id_eq] using
      space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset hvK hstrict)
  have hCenterJ (j : Bool) : center j ∈ J j := by
    change (s j).centroid ℝ id ∈ J j
    exact hcenter j ▸ (G j _).property
  have hCenterA (j : Bool) : center j ∈ (M arc).space := by
    have hm := ((M arc).barycentricDualBlock (s j)).vertices_subset_space
      ((M arc).faceCentroid_mem_barycentricDualBlock_vertices (hs j))
    exact (M arc).barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le ((M arc).barycentricDualBlock_le (s j)) hm)
  have hne : center false ≠ center true := fun he =>
    Set.disjoint_left.mp hdisj (hCenterJ false) (he ▸ hCenterJ true)
  have hboundary : bZ = {center false, center true} := by
    obtain ⟨x, y, hxy, hp⟩ := hZ.exists_boundary_eq_pair
    have hm (j : Bool) : center j ∈ ({x, y} : Set E) := hp.subset
      ⟨⟨hJV j (hCenterJ j), hCenterA j⟩, Or.inl (hJlink j (hCenterJ j))⟩
    rw [hp]
    rcases hm false with h₀ | h₀ <;> rcases hm true with h₁ | h₁
    · exact False.elim (hne (h₀.trans h₁.symm))
    · simp only [h₀, show center true = y from h₁]
    · rw [h₀, show center true = x from h₁, pair_comm]
    · exact False.elim (hne (h₀.trans h₁.symm))
  have hAligned (j : Bool) : (aligned j).IsFinitePL :=
    signedTubeDiamondReflection_trans_isFinitePL (hG j) (eta j)
  have hAlignedQ (j : Bool) := signedDiamond_reflection_coordinate_quarters (J j) c (eta j) (G j) (hQ j)
  have hAlignedRad (j : Bool) (i : Fin 2) (sign : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius i sign ↔ (aligned j x : E) ∈ rad j i sign :=
    signedDiamond_coordinate_radius_iff (J j) c (aligned j) (hAlignedQ j) i sign x
  have hAlignedCenter (j : Bool) : (aligned j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = center j := by
    have heq : signedTubeDiamondReflection (eta j)
        ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
        ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ :=
      Subtype.ext (signedTubeReflection_zero (eta j))
    change (G j (signedTubeDiamondReflection (eta j) _) : E) = center j
    rw [heq]
    exact hcenter j
  have hRadTarget (j : Bool) (i : Fin 2) (sign : Bool) : rad j i sign ⊆ J j :=
    fun _ hz => hz.1
  have hrad (j : Bool) (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (rad j i sign) {center j, corner j i sign} := by
    have h := isFinitePLBallPair_signed_diamond_radius_image (aligned j) (hAligned j) i sign
      (hRadTarget j i sign) (hAlignedRad j i sign)
    simpa only [hAlignedCenter] using h
  have hRadOuter (j : Bool) (i : Fin 2) (sign : Bool) : rad j i sign ⊆ outer i sign := by
    intro z hz
    have hzV := hJV j hz.1
    have hzS : z ∈ (M (sheet i)).space := (hsheet i z (hVK hzV)).mpr
      ((hsheets i (g z) (hVB hzV)).mpr ⟨interior_subset (hinside z hzV), hz.2.1⟩)
    exact ⟨⟨hD.superset hzV, hzS, hz.2.2⟩, Or.inl (hJlink j hz.1)⟩
  have hcorner (j : Bool) (i : Fin 2) (sign : Bool) : center j ≠ corner j i sign := by
    intro he
    have hx := (aligned j).injective (Subtype.ext ((hAlignedCenter j).trans he))
    exact signedTube_corner_ne_center i sign (congrArg Subtype.val hx).symm
  have houter (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (outer i sign) {center false, center true} := by
    have h := (hfaces i sign).2
    change IsFinitePLBallPair ℝ (outer i sign) bZ at h
    rw [hboundary] at h
    exact h
  have hcontact (i : Fin 2) (sign : Bool) : Z ∩ outer i sign = {center false, center true} := by
    rw [← hboundary]
    ext z
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, (hfaces i sign).1.1 (Or.inl h.1), h.2⟩⟩
  have hZ' : IsFinitePLBallPair ℝ Z {center false, center true} := by
    rw [hboundary] at hZ
    exact hZ
  exact exists_signed_endpoint_half_face_maps center corner J rad face outer bArc hbArc
    hZ' hZAaxis hne (fun i sign => (hfaces i sign).1) houter hcontact hrad
    hRadOuter hRadTarget hcorner
    (fun i sign => hdisj.mono (hRadTarget false i sign) (hRadTarget true i sign))
    aligned hAligned hAlignedRad hAlignedCenter (fun _ _ _ => rfl)

open Classical in
theorem exists_original_interior_half_face_maps_of_joint_maps
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hvFr : (g v : X) ∉ frontier R)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space)
    (G : ∀ j, signedTubeDiamond ≃ₜ (K.barycentricDualBlock (s j)).space)
    (hG : ∀ j, (G j).IsFinitePL) (eta : Bool → Fin 2 → Bool)
    (hQ : ∀ j eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G j x : E) ∈ signedCoordinateSector (K.barycentricDualBlock (s j)).space
          (fun i z => B (g z) i.castSucc) (eta j) eps delta)
    (hcenter : ∀ j, (G j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) =
        (s j).centroid ℝ id)
    (bArc : Icc (0 : ℝ) 1 ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let Z := V.space ∩ (M arc).space
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let outer := fun i sign => {z | z ∈ face i sign ∧
      (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1)
      (axis : Icc (α : ℝ) (β : ℝ) ≃ₜ Z) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      axis.IsFinitePL ∧
      (∀ t, (axis t : E) = bArc ⟨t, hsub t.property⟩) ∧
      (∀ j, (axis ⟨if j then (β : ℝ) else (α : ℝ),
        by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
          (s (index j)).centroid ℝ id) ∧
      ∀ i sign, ∃ map : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign,
        map.IsFinitePL ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (map ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            bArc ⟨t, hsub t.property⟩) ∧
        (∀ j (x : signedTubeRadius i sign),
          (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
              aligned (index j) ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : P2 × ℝ) ∈ signedTubePrismAxis α β ↔ (map x : E) ∈ Z) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : P2 × ℝ) ∈ signedTubePrismOuter i sign α β ↔ (map x : E) ∈ outer i sign) := by
  exact exists_original_interior_half_face_maps_of_joint_maps_of_axis_superset hAC hAR S K H g hg hgPL M hMK
    reg fr arc sheet hreg hfr harc hsheet v B hsource hface haxis hsheets hregion hvFr
    s hs hcard hvs hdisj G hG eta hQ hcenter bArc hbArc inter_subset_right

end PoincareConjecture.M76.Dehn
