import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointHalfFaceMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismVolumeMap

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_endpoint_sector_maps
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
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source →
        (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2)
    (v : (M arc).vertices) (hvs : (v : E) ∈ s)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (hvFr : (g v : X) ∈ frontier R)
    (bArc : Icc (0 : ℝ) 1 ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let J := K.barycentricDualBlock s
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    ∃ (p : (M arc).vertices) (jointMap : signedTubeDiamond ≃ₜ J.space)
      (eta : Fin 2 → Bool) (footMap : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space))
      (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1) (reverseEnds : Bool),
      let alignedFoot := (signedTubeDiamondReflection eta).trans footMap
      let index := fun j : Bool => if reverseEnds then !j else j
      let localSign := fun i sign => signedTubeReindex (eta i.rev) sign
      ∃ halfMap : ∀ i sign,
          ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i (localSign i sign),
        jointMap.IsFinitePL ∧ alignedFoot.IsFinitePL ∧
        (∀ i sign, (halfMap i sign).IsFinitePL) ∧
        (∀ i sign (t : Icc (α : ℝ) (β : ℝ)),
          (halfMap i sign ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            bArc ⟨t, hsub t.property⟩) ∧
        ∀ signs : Fin 2 → Bool,
          let localSigns := fun i => signedTubeReindex (eta i) (signs i)
          let sector := D.space ∩ {z | ∀ i : Fin 2,
            if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
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
                if index j then
                  (jointMap ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ : E)
                else
                  (alignedFoot ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ : E)) ∧
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
  let J := K.barycentricDualBlock s
  let Z := V.space ∩ (M arc).space
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  obtain ⟨p, jointMap, eta, footMap, hJoint, hFoot, hJointQuarter, hFootQuarter, hGeometry,
    α, β, hlt, hsub, axis, reverseEnds, _, _, _, hHalf⟩ :=
    exists_original_endpoint_half_face_maps hAC hAR hAF S K F hF H hH g hg hgPL M hMK
      hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard v hvs hregion hvFr bArc hbArc
  let alignedFoot := (signedTubeDiamondReflection eta).trans footMap
  let index := fun j : Bool => if reverseEnds then !j else j
  choose halfMap hHalfPL hAxis hEnd hAxisMem hOuterMem using hHalf
  refine ⟨p, jointMap, eta, footMap, α, β, hlt, hsub, reverseEnds,
    halfMap, hJoint, hFoot, hHalfPL, hAxis, ?_⟩
  intro signs
  let localSigns := fun i => signedTubeReindex (eta i) (signs i)
  let faces := fun i => face i (localSigns i.rev)
  let quarters := fun j : Bool => if j then
    {z | z ∈ J.space ∧
      (if signs 0 then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
      if signs 1 then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
    else {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
  have hQuarter (j : Bool) :
      ∃ qmap : signedTubeQuarter (signs 0) (signs 1) ≃ₜ quarters j,
        qmap.IsFinitePL ∧ ∀ x : signedTubeQuarter (signs 0) (signs 1),
          (qmap x : E) = if j then
            (jointMap ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ : E)
          else (alignedFoot ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ : E) := by
    cases j
    · have hvec : ![signedTubeReindex (eta 0) (signs 0),
          signedTubeReindex (eta 1) (signs 1)] = localSigns := by
        funext i
        fin_cases i <;> rfl
      have hm := hFootQuarter (signs 0) (signs 1)
      rw [hvec] at hm
      exact exists_signed_diamond_quarter_restriction alignedFoot hFoot (signs 0) (signs 1)
        (fun _ hx => ⟨hx.1, hx.2.1⟩) hm
    · exact exists_signed_diamond_quarter_restriction jointMap hJoint (signs 0) (signs 1)
        (fun _ hx => hx.1) (hJointQuarter (signs 0) (signs 1))
  choose qmap hqmap hqval using hQuarter
  obtain ⟨hInter, hDisj, hContact, rim, hDisk, hSub, hOut, hBall⟩ := hGeometry signs
  have hUnion : quarters (index false) ∪ quarters (index true) = quarters false ∪ quarters true := by
    cases reverseEnds <;> simp [index, union_comm]
  have hD : IsFinitePLBallPair P2 ((faces 0 ∪ faces 1) ∪
      (quarters (index false) ∪ quarters (index true))) rim := by
    rw [hUnion]
    exact hDisk
  have hS : (faces 0 ∪ faces 1) ∪ (quarters (index false) ∪ quarters (index true)) ⊆
      {z | z ∈ D.space ∧
        (∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0) ∧
        (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)} := by
    rw [hUnion]
    exact hSub
  have hO : ({z | z ∈ D.space ∧
        (∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0) ∧
        (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)} \
      ((faces 0 ∪ faces 1) ∪ (quarters (index false) ∪ quarters (index true)))).Nonempty := by
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
  have hC (j : Bool) (i : Fin 2) (x : signedTubeQuarter (signs 0) (signs 1)) :
      (qmap (index j) x : E) ∈ faces i ↔ (x : P2) ∈ signedTubeRadius i (signs i.rev) := by
    rw [hqval]
    exact hContact (index j) i
      ⟨x, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, x.property⟩⟩⟩ x.property
  have hK (i : Fin 2) (j : Bool) (x : signedTubeRadius i (signs i.rev)) :
      (halfMap i (signs i.rev) ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
        by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
      qmap (index j) ⟨x, signedTubeRadius_subset_quarter signs i x.property⟩ := by
    rw [hqval]
    exact hEnd i (signs i.rev) j x
  obtain ⟨map, hmap, hFace, hEndQuarter, hBoundary⟩ := exists_signed_sector_volume_map
    signs α β hlt faces (fun j => quarters (index j)) Z _ _ rim hBall hD hS hO
      (fun i => halfMap i (signs i.rev)) (fun j => qmap (index j))
      (fun i => hHalfPL i (signs i.rev)) (fun j => hqmap (index j)) hInter hd
      (fun t => (bArc ⟨t, hsub t.property⟩ : E)) hA
      (fun i => hAxis i (signs i.rev)) hC hK
  refine ⟨map, hmap, hFace, ?_, ?_, ?_⟩
  · intro j x
    exact (hEndQuarter j x).trans (hqval (index j) x)
  · intro t
    exact (hFace 0 ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩).trans (hAxis 0 (signs 1) t)
  · intro x
    simpa only [mem_setOf_eq, mem_inter_iff, and_assoc] using hBoundary x

end PoincareConjecture.M76.Dehn
