import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcInteriorHalfFaceMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcInteriorSectorBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcBlockCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismVolumeMap

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_interior_sector_maps_of_joint_maps_of_axis_superset
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
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      ∃ halfMap : ∀ i sign,
          ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign,
        (∀ i sign, (halfMap i sign).IsFinitePL) ∧
        (∀ i sign (t : Icc (α : ℝ) (β : ℝ)),
          (halfMap i sign ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            bArc ⟨t, hsub t.property⟩) ∧
        ∀ signs : Fin 2 → Bool,
          let sector := D.space ∩ {z | ∀ i : Fin 2,
            if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
          let boundary := {z | z ∈ sector ∧
            (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
          ∃ map : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ sector,
            map.IsFinitePL ∧
            (∀ i (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc (α : ℝ) (β : ℝ))),
              (map ⟨x, signedTubeRadius_subset_quarter signs i x.property.1, x.property.2⟩ : E) =
                halfMap i (signs i.rev) x) ∧
            (∀ j (x : signedTubeQuarter (signs 0) (signs 1)),
              (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
                by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
                  aligned (index j) ⟨x, mem_iUnion.mpr
                    ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩) ∧
            (∀ t : Icc (α : ℝ) (β : ℝ),
              (map ⟨((0, 0), t), signedTubeRadius_subset_quarter signs 0
                (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
            ∀ x : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)),
              (x : P2 × ℝ) ∈
                (signedTubeOuterArc (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)) ∪
                  signedTubeSectorPrescribed (signs 0) (signs 1) α β ↔ (map x : E) ∈ boundary := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let Z := V.space ∩ (M arc).space
  let J := fun j => (K.barycentricDualBlock (s j)).space
  let c := fun (i : Fin 2) z => B v (g z) i.castSucc
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
  obtain ⟨α, β, hlt, hsub, axis, reverseEnds, haxisPL, haxisval, horder, hHalf⟩ :=
    exists_original_interior_half_face_maps_of_joint_maps_of_axis_superset hAC hAR S K H g hg hgPL M hMK
      reg fr arc sheet hreg hfr harc hsheet v (B v) (hB v).1 (hB v).2.1 (hB v).2.2.1
      (hB v).2.2.2 hregion hvFr s hs hcard hvs hdisj G hG eta hQ hcenter bArc hbArc hZAaxis
  let index := fun j : Bool => if reverseEnds then !j else j
  choose halfMap hHalfPL hAxis hEnd hAxisMem hOuterMem using hHalf
  have hAligned (j : Bool) : (aligned j).IsFinitePL :=
    signedTubeDiamondReflection_trans_isFinitePL (hG j) (eta j)
  have hAlignedQ (j : Bool) := signedDiamond_reflection_coordinate_quarters (J j) c (eta j) (G j) (hQ j)
  obtain ⟨hcoord, hAxisSet⟩ := original_vertex_block_coordinate_marks S K
    (fun z => (g z : X)) M hMK reg arc sheet hreg harc hsheet v (B v)
    (hB v).1 (hB v).2.2.1 (hB v).2.2.2
  obtain ⟨hD, _, _⟩ := original_interior_vertex_region_eq hAC hAR K H g hg hgPL M hMK
    reg fr arc hreg hfr harc v (B v) (hB v).1 (hB v).2.1 hvFr
  have hJD (j : Bool) : J j ⊆ D.space := by
    rw [hD]
    exact space_subset_of_le (K.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (hvs j)))
  refine ⟨α, β, hlt, hsub, reverseEnds, halfMap, hHalfPL, hAxis, ?_⟩
  intro signs
  let cuts := {z | ∀ i : Fin 2,
    if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
  let faces := fun i => face i (signs i.rev)
  let quarters := fun j => J j ∩ cuts
  let boundary := {z | z ∈ D.space ∧ z ∈ cuts ∧
    (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
  have hQuarter (j : Bool) : ∃ qmap : signedTubeQuarter (signs 0) (signs 1) ≃ₜ quarters j,
      qmap.IsFinitePL ∧ ∀ x : signedTubeQuarter (signs 0) (signs 1),
        (qmap x : E) = aligned j ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ := by
    apply exists_signed_diamond_quarter_restriction (aligned j) (hAligned j)
      (signs 0) (signs 1) inter_subset_left
    intro x
    simpa [aligned, signedCoordinateSector, signedCoordinateCut, signedTubeReindex, quarters,
      cuts, c, Fin.forall_fin_two] using hAlignedQ j (signs 0) (signs 1) x
  choose qmap hqmap hqval using hQuarter
  obtain ⟨rim, hDisk, hSub, hOut, hBall, _, hInter, _, hDisj⟩ :=
    exists_original_interior_sector_boundary_disk hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj signs
  have hUnion : quarters (index false) ∪ quarters (index true) = quarters false ∪ quarters true := by
    cases reverseEnds <;> simp [index, union_comm]
  have hDisk' : IsFinitePLBallPair P2 ((faces 0 ∪ faces 1) ∪
      (quarters (index false) ∪ quarters (index true))) rim := by
    rw [hUnion]
    exact hDisk
  have hSub' : (faces 0 ∪ faces 1) ∪ (quarters (index false) ∪ quarters (index true)) ⊆ boundary := by
    rw [hUnion]
    exact hSub
  have hOut' : (boundary \ ((faces 0 ∪ faces 1) ∪
      (quarters (index false) ∪ quarters (index true)))).Nonempty := by
    rw [hUnion]
    exact hOut
  have hd : Disjoint (quarters (index false)) (quarters (index true)) := by
    cases reverseEnds
    · exact hDisj
    · exact hDisj.symm
  have hA (x : ↥(signedTubeRadius 0 (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ))) :
      (x : P2 × ℝ).1 = (0, 0) ↔ (halfMap 0 (signs 1) x : E) ∈ Z := by
    simpa only [signedTubePrismAxis, mem_prod, mem_singleton_iff, x.property.2, and_true]
      using hAxisMem 0 (signs 1) x
  have hContact (j : Bool) (i : Fin 2) (x : signedTubeQuarter (signs 0) (signs 1)) :
      (qmap (index j) x : E) ∈ faces i ↔ (x : P2) ∈ signedTubeRadius i (signs i.rev) := by
    rw [hqval]
    let xd : signedTubeDiamond := ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩
    have hzJ := (aligned (index j) xd).property
    have hzD := hJD (index j) hzJ
    have hi : (aligned (index j) xd : E) ∈ faces i ↔
        (aligned (index j) xd : E) ∈ signedCoordinateFace (J (index j)) c (fun _ => true) i (signs i.rev) := by
      exact ⟨fun h => ⟨hzJ, (hcoord i _ hzD).mp h.2.1, h.2.2⟩,
        fun h => ⟨hzD, (hcoord i _ hzD).mpr h.2.1, h.2.2⟩⟩
    exact hi.trans (signedDiamond_coordinate_radius_iff (J (index j)) c
      (aligned (index j)) (hAlignedQ (index j)) i (signs i.rev) xd).symm
  have hKeep (i : Fin 2) (j : Bool) (x : signedTubeRadius i (signs i.rev)) :
      (halfMap i (signs i.rev) ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
        by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
        qmap (index j) ⟨x, signedTubeRadius_subset_quarter signs i x.property⟩ := by
    rw [hqval]
    exact hEnd i (signs i.rev) j x
  obtain ⟨map, hmap, hFace, hEndQuarter, hBoundary⟩ := exists_signed_sector_volume_map
    signs α β hlt faces (fun j => quarters (index j)) Z _ _ rim hBall hDisk' hSub' hOut'
      (fun i => halfMap i (signs i.rev)) (fun j => qmap (index j))
      (fun i => hHalfPL i (signs i.rev)) (fun j => hqmap (index j)) hInter hd
      (fun t => (bArc ⟨t, hsub t.property⟩ : E)) hA
      (fun i => hAxis i (signs i.rev)) hContact hKeep
  refine ⟨map, hmap, hFace, ?_, ?_, ?_⟩
  · intro j x
    exact (hEndQuarter j x).trans (hqval (index j) x)
  · intro t
    exact (hFace 0 ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩).trans (hAxis 0 (signs 1) t)
  · intro x
    simpa only [mem_setOf_eq, mem_inter_iff, and_assoc] using hBoundary x

open Classical in
theorem exists_original_interior_sector_maps_of_joint_maps
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
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let aligned := fun j => (signedTubeDiamondReflection (eta j)).trans (G j)
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      ∃ halfMap : ∀ i sign,
          ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign,
        (∀ i sign, (halfMap i sign).IsFinitePL) ∧
        (∀ i sign (t : Icc (α : ℝ) (β : ℝ)),
          (halfMap i sign ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            bArc ⟨t, hsub t.property⟩) ∧
        ∀ signs : Fin 2 → Bool,
          let sector := D.space ∩ {z | ∀ i : Fin 2,
            if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
          let boundary := {z | z ∈ sector ∧
            (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
          ∃ map : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ sector,
            map.IsFinitePL ∧
            (∀ i (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc (α : ℝ) (β : ℝ))),
              (map ⟨x, signedTubeRadius_subset_quarter signs i x.property.1, x.property.2⟩ : E) =
                halfMap i (signs i.rev) x) ∧
            (∀ j (x : signedTubeQuarter (signs 0) (signs 1)),
              (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
                by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
                  aligned (index j) ⟨x, mem_iUnion.mpr
                    ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩) ∧
            (∀ t : Icc (α : ℝ) (β : ℝ),
              (map ⟨((0, 0), t), signedTubeRadius_subset_quarter signs 0
                (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
            ∀ x : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)),
              (x : P2 × ℝ) ∈
                (signedTubeOuterArc (signs 0) (signs 1) ×ˢ Icc (α : ℝ) (β : ℝ)) ∪
                  signedTubeSectorPrescribed (signs 0) (signs 1) α β ↔ (map x : E) ∈ boundary := by
  exact exists_original_interior_sector_maps_of_joint_maps_of_axis_superset hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull
    reg fr arc sheet hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj
    G hG eta hQ hcenter bArc hbArc inter_subset_right

end PoincareConjecture.M76.Dehn
