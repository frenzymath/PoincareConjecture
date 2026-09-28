import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcInteriorSectorMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedSectorBlockGluing

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_interior_block_map_of_joint_maps_of_axis_superset
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (v : (M arc).vertices) (hvFr : (g v : X) ∉ frontier R)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space)
    (G : ∀ j, signedTubeDiamond ≃ₜ (K.barycentricDualBlock (s j)).space)
    (hG : ∀ j, (G j).IsFinitePL) (eta : Bool → Fin 2 → Bool)
    (hQ : ∀ j eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G j x : E) ∈ signedCoordinateSector (K.barycentricDualBlock (s j)).space
          (fun i z => B v (g z) i.castSucc) (eta j) eps delta)
    (hcenter : ∀ j, (G j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) =
        (s j).centroid ℝ id)
    {Aaxis : Set E} (bArc : Icc (0 : ℝ) 1 ≃ₜ Aaxis) (hbArc : bArc.IsFinitePL)
    (hZAaxis : (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space ⊆ Aaxis) :
    let D := (M reg).barycentricDualBlock {(v : E)}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      ∃ (halfMap : ∀ i sign,
          ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign)
        (map : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ D.space),
        map.IsFinitePL ∧ (∀ i sign, (halfMap i sign).IsFinitePL) ∧
        (∀ i sign (x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ))),
          (map ⟨x, signedTubeRadius_subset_diamond i sign x.property.1, x.property.2⟩ : E) =
            halfMap i sign x) ∧
        (∀ j (x : signedTubeDiamond),
          (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) = aligned (index j) x) ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
            (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
        ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
            (map x : E) ∈ D.space ∩ {z | ∀ i : Fin 2,
              if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
                else B v (g z) i.castSucc ≤ 0} := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let Z := V.space ∩ (M arc).space
  obtain ⟨α, β, hlt, hsub, reverseEnds, halfMap, hHalfPL, hHalfAxis, hSectors⟩ :=
    exists_original_interior_sector_maps_of_joint_maps_of_axis_superset hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs
      hdisj G hG eta hQ hcenter bArc hbArc hZAaxis
  let coords := fun (i : Fin 2) (z : E) => B v (g z) i.castSucc
  let sector := fun eps delta : Bool => D.space ∩ {z | ∀ i : Fin 2,
    if (![eps, delta] i) then 0 ≤ coords i z else coords i z ≤ 0}
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ coords i.rev z else coords i.rev z ≤ 0}
  obtain ⟨hSheet, hAxis⟩ := original_vertex_block_coordinate_marks S K (fun z => (g z : X))
    M hMK reg arc sheet hreg harc hsheet v (B v) (hB v).1 (hB v).2.2.1 (hB v).2.2.2
  have hSector (eps delta : Bool) : sector eps delta =
      signedCoordinateSector D.space coords (fun _ => true) eps delta := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, hz.2 0, hz.2 1⟩
    · rintro ⟨hd, h0, h1⟩
      refine ⟨hd, ?_⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
  have hFace (i : Fin 2) (sign : Bool) : face i sign =
      signedCoordinateFace D.space coords (fun _ => true) i sign := by
    ext z
    exact ⟨fun hz => ⟨hz.1, (hSheet i z hz.1).mp hz.2.1, hz.2.2⟩,
      fun hz => ⟨hz.1, (hSheet i z hz.1).mpr hz.2.1, hz.2.2⟩⟩
  have hAxisEq : {z | z ∈ D.space ∧ coords 0 z = 0 ∧ coords 1 z = 0} = Z := hAxis
  have hInter (eps delta : Bool) :
      sector eps delta ∩ sector eps (!delta) = face 1 eps ∧
      sector eps delta ∩ sector (!eps) delta = face 0 delta ∧
      sector eps delta ∩ sector (!eps) (!delta) = Z := by
    have h := signedCoordinateSector_incidence D.space coords (fun _ => true) eps delta
    rw [hSector, hSector, hSector, hSector, hFace, hFace, ← hAxisEq]
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hMeet (eps delta : Bool) : face 0 delta ∩ face 1 eps = Z := by
    rw [hFace, hFace, ← hAxisEq]
    exact (signedCoordinateSector_incidence D.space coords (fun _ => true) eps delta).2.2.2
  have hCover : (⋃ eps, ⋃ delta, sector eps delta) = D.space := by
    simp only [hSector]
    exact signedCoordinateSector_cover D.space coords (fun _ => true)
  choose maps hMaps hMapsFace hMapsEnd hMapsAxis hMapsBoundary using
    fun eps delta => hSectors ![eps, delta]
  have h0 (eps delta : Bool) (x : ↥(signedTubeRadius 0 delta ×ˢ Icc (α : ℝ) (β : ℝ))) :
      (maps eps delta ⟨x, (signedTube_quarter_ball eps delta).1
        (Or.inr (Or.inl x.property.1)), x.property.2⟩ : E) = halfMap 0 delta x :=
    hMapsFace eps delta 0 x
  have h1 (eps delta : Bool) (x : ↥(signedTubeRadius 1 eps ×ˢ Icc (α : ℝ) (β : ℝ))) :
      (maps eps delta ⟨x, (signedTube_quarter_ball eps delta).1
        (Or.inr (Or.inr x.property.1)), x.property.2⟩ : E) = halfMap 1 eps x :=
    hMapsFace eps delta 1 x
  obtain ⟨map, hmap, hkeep, hmem⟩ := exists_signed_sector_block_map α β sector face Z D.space
    halfMap maps hMaps hInter hMeet hCover h0 h1
      (fun t => (bArc ⟨t, hsub t.property⟩ : E)) hMapsAxis
  refine ⟨α, β, hlt, hsub, reverseEnds, halfMap, map, hmap, hHalfPL, ?_, ?_, ?_, hmem⟩
  · intro i sign x
    fin_cases i
    · exact (hkeep false sign ⟨x, (signedTube_quarter_ball false sign).1
        (Or.inr (Or.inl x.property.1)), x.property.2⟩).trans (h0 false sign x)
    · exact (hkeep sign false ⟨x, (signedTube_quarter_ball sign false).1
        (Or.inr (Or.inr x.property.1)), x.property.2⟩).trans (h1 sign false x)
  · intro j x
    obtain ⟨eps, heps⟩ := mem_iUnion.mp x.property
    obtain ⟨delta, hx⟩ := mem_iUnion.mp heps
    exact (hkeep eps delta ⟨(x, if j then (β : ℝ) else (α : ℝ)), hx,
      by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩).trans (hMapsEnd eps delta j ⟨x, hx⟩)
  · intro t
    exact (hkeep false false ⟨((0, 0), t), signedTube_center_mem, t.property⟩).trans
      (hMapsAxis false false t)

open Classical in
theorem exists_original_interior_block_map_of_joint_maps
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (v : (M arc).vertices) (hvFr : (g v : X) ∉ frontier R)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space)
    (G : ∀ j, signedTubeDiamond ≃ₜ (K.barycentricDualBlock (s j)).space)
    (hG : ∀ j, (G j).IsFinitePL) (eta : Bool → Fin 2 → Bool)
    (hQ : ∀ j eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G j x : E) ∈ signedCoordinateSector (K.barycentricDualBlock (s j)).space
          (fun i z => B v (g z) i.castSucc) (eta j) eps delta)
    (hcenter : ∀ j, (G j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) =
        (s j).centroid ℝ id)
    (bArc : Icc (0 : ℝ) 1 ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL) :
    let D := (M reg).barycentricDualBlock {(v : E)}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      ∃ (halfMap : ∀ i sign,
          ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign)
        (map : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ D.space),
        map.IsFinitePL ∧ (∀ i sign, (halfMap i sign).IsFinitePL) ∧
        (∀ i sign (x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ))),
          (map ⟨x, signedTubeRadius_subset_diamond i sign x.property.1, x.property.2⟩ : E) =
            halfMap i sign x) ∧
        (∀ j (x : signedTubeDiamond),
          (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) = aligned (index j) x) ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
            (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
        ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (α : ℝ) (β : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
            (map x : E) ∈ D.space ∩ {z | ∀ i : Fin 2,
              if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
                else B v (g z) i.castSucc ≤ 0} := by
  exact exists_original_interior_block_map_of_joint_maps_of_axis_superset hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull
    reg fr arc sheet hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj
    G hG eta hQ hcenter bArc hbArc inter_subset_right

end PoincareConjecture.M76.Dehn
