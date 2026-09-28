import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointJointBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedEndpointHalfFaceMaps









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_endpoint_half_face_maps
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
    let Z := V.space ∩ (M arc).space
    let foot := fun signs : Fin 2 → Bool =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let outer := fun i sign =>
      {z | z ∈ face i sign ∧ (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
    ∃ (p : (M arc).vertices) (jointMap : signedTubeDiamond ≃ₜ J.space)
      (eta : Fin 2 → Bool) (footMap : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space)),
      let alignedFoot := (signedTubeDiamondReflection eta).trans footMap
      let localSign := fun i sign => signedTubeReindex (eta i.rev) sign
      jointMap.IsFinitePL ∧ alignedFoot.IsFinitePL ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔
          (jointMap x : E) ∈ {z | z ∈ J.space ∧
            (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
            if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}) ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔
          (alignedFoot x : E) ∈ foot ![signedTubeReindex (eta 0) eps,
            signedTubeReindex (eta 1) delta]) ∧
      (∀ signs : Fin 2 → Bool,
        let localSigns := fun i => signedTubeReindex (eta i) (signs i)
        let faces := fun i => face i (localSigns i.rev)
        let quarters := fun j : Bool => if j then
          {z | z ∈ J.space ∧
            (if signs 0 then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
            if signs 1 then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
          else foot localSigns
        let prescribed := (faces 0 ∪ faces 1) ∪ (quarters false ∪ quarters true)
        let boundary := {z | z ∈ D.space ∧
          (∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc
            else B v (g z) i.castSucc ≤ 0) ∧
          (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
        faces 0 ∩ faces 1 = Z ∧ Disjoint (quarters false) (quarters true) ∧
        (∀ (j : Bool) i (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeQuarter (signs 0) (signs 1) →
          ((if j then (jointMap x : E) else (alignedFoot x : E)) ∈ faces i ↔
            (x : P2) ∈ signedTubeRadius i (signs i.rev))) ∧
        ∃ rim : Set E, IsFinitePLBallPair P2 prescribed rim ∧
          prescribed ⊆ boundary ∧ (boundary \ prescribed).Nonempty ∧
          IsFinitePLBallPair V3
            (D.space ∩ {z | ∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc
              else B v (g z) i.castSucc ≤ 0}) boundary) ∧
      ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
        (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1)
        (axis : Icc (α : ℝ) (β : ℝ) ≃ₜ Z) (reverseEnds : Bool),
        let index := fun j : Bool => if reverseEnds then !j else j
        axis.IsFinitePL ∧ (∀ t, (axis t : E) = (bArc ⟨t, hsub t.property⟩ : E)) ∧
        (∀ j, (axis ⟨if j then (β : ℝ) else (α : ℝ),
          by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
            if index j then s.centroid ℝ id else (v : E)) ∧
        ∀ i sign, ∃ map : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i (localSign i sign),
          map.IsFinitePL ∧
          (∀ t : Icc (α : ℝ) (β : ℝ),
            (map ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
              bArc ⟨t, hsub t.property⟩) ∧
          (∀ j (x : signedTubeRadius i sign),
            (map ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
              by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
                if index j then (jointMap ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E)
                else (alignedFoot ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E)) ∧
          (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
            (x : P2 × ℝ) ∈ signedTubePrismAxis α β ↔ (map x : E) ∈ Z) ∧
          ∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
            (x : P2 × ℝ) ∈ signedTubePrismOuter i sign α β ↔
              (map x : E) ∈ outer i (localSign i sign) := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let J := K.barycentricDualBlock s
  let m := s.centroid ℝ id
  let Z := V.space ∩ (M arc).space
  let footRadius := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let outer := fun i sign =>
    {z | z ∈ face i sign ∧ (z ∈ (V.link v).space ∨ z ∈ (M fr).space)}
  obtain ⟨C0, theta, p, T, G, eta, bFoot, footMap, hC, hcv, hzero,
    htheta, hthetaInv, hlink, hmarks, hmiss, hJV, hJarc, hJlink, hvm, hZboundary,
    hZ, hfaces, hFootGeometry, hFootRegion, hEndGeometry, hG, hGquarters,
    hGradii, hGcenter, hGcorners, hFoot, hFootQuarter, hFootRadius, hFootEnds,
    hFootOuter, hAlignedFoot, hAlignedQuarter, hAlignedRadius, hSectors⟩ :=
    exists_original_endpoint_joint_boundary_disk hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard v hvs hregion hvFr
  let a := fun i sign => (T i sign).centroid ℝ id
  let jointRadius := fun i sign => segment ℝ m (a i sign)
  let localSign := fun (i : Fin 2) (sign : Bool) => signedTubeReindex (eta i.rev) sign
  let alignedFoot := (signedTubeDiamondReflection eta).trans footMap
  let center := fun j : Bool => if j then m else (v : E)
  let corner := fun (j : Bool) i sign => if j then a i sign else bFoot i (localSign i sign)
  let target := fun j : Bool => if j then J.space else V.space ∩ (M fr).space
  let rad := fun (j : Bool) i sign => if j then jointRadius i sign else footRadius i (localSign i sign)
  let maps : ∀ j, signedTubeDiamond ≃ₜ target j := fun j => by
    cases j
    · exact alignedFoot
    · exact G
  have hmaps (j : Bool) : (maps j).IsFinitePL := by
    cases j
    · exact hAlignedFoot
    · exact hG
  have hmapRad (j : Bool) (i : Fin 2) (sign : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius i sign ↔ (maps j x : E) ∈ rad j i sign := by
    cases j
    · exact hAlignedRadius i sign x
    · exact hGradii i sign x
  have hmapCenter (j : Bool) : (maps j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = center j := by
    cases j
    · have heq : signedTubeDiamondReflection eta
          ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
        ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ :=
          Subtype.ext (signedTubeReflection_zero eta)
      change (footMap (signedTubeDiamondReflection eta _) : E) = (v : E)
      rw [heq]
      exact (hFootEnds 0 false ⟨(0, 0), left_mem_segment ℝ _ _⟩).1.mpr rfl
    · exact hGcenter
  have hmapCorner (j : Bool) (i : Fin 2) (sign : Bool) :
      (maps j ⟨signedTubeCorner i sign,
        signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E) = corner j i sign := by
    cases j
    · have heq : signedTubeDiamondReflection eta
          ⟨signedTubeCorner i sign, signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ =
        ⟨signedTubeCorner i (localSign i sign),
          signedTubeRadius_subset_diamond i _ (right_mem_segment ℝ _ _)⟩ :=
            Subtype.ext (signedTubeReflection_corner eta i sign)
      change (footMap (signedTubeDiamondReflection eta _) : E) = bFoot i (localSign i sign)
      rw [heq]
      exact (hFootEnds i (localSign i sign)
        ⟨signedTubeCorner i (localSign i sign), right_mem_segment ℝ _ _⟩).2.mpr rfl
    · exact hGcorners i sign
  have hZ' : IsFinitePLBallPair ℝ Z {center false, center true} := by
    rw [hZboundary] at hZ
    exact hZ
  have hOuter (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (outer i (localSign i sign)) {center false, center true} := by
    have h := (hfaces i (localSign i sign)).2
    rw [hZboundary] at h
    exact h
  have hrad (j : Bool) (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (rad j i sign) {center j, corner j i sign} := by
    cases j
    · exact (hFootGeometry i (localSign i sign)).2.1
    · exact (hEndGeometry i sign).1
  have hRadOuter (j : Bool) (i : Fin 2) (sign : Bool) :
      rad j i sign ⊆ outer i (localSign i sign) := by
    cases j
    · exact (hEndGeometry i sign).2.2.1
    · exact (hEndGeometry i sign).2.1
  have hRadTarget (j : Bool) (i : Fin 2) (sign : Bool) : rad j i sign ⊆ target j := by
    cases j
    · exact fun _ hz => ⟨hz.1, hz.2.1⟩
    · exact (hEndGeometry i sign).2.2.2.2.2.2
  have hcorner (j : Bool) (i : Fin 2) (sign : Bool) : center j ≠ corner j i sign := by
    cases j
    · exact (hFootGeometry i (localSign i sign)).1.symm
    · exact (hEndGeometry i sign).2.2.2.2.2.1.symm
  obtain ⟨α, β, hlt, hsub, axis, reverseEnds, haxis, haxisval, horder, hHalfFaces⟩ :=
    exists_signed_endpoint_half_face_maps center corner target rad
      (fun i sign => face i (localSign i sign)) (fun i sign => outer i (localSign i sign))
      bArc hbArc hZ' inter_subset_right hvm
      (fun i sign => (hfaces i (localSign i sign)).1) hOuter
      (fun i sign => (hEndGeometry i sign).2.2.2.2.1) hrad hRadOuter hRadTarget hcorner
      (fun i sign => (hEndGeometry i sign).2.2.2.1) maps hmaps hmapRad hmapCenter hmapCorner
  refine ⟨p, G, eta, footMap, hG, hAlignedFoot, hGquarters, hAlignedQuarter, ?_,
    α, β, hlt, hsub, axis, reverseEnds, haxis, haxisval, horder, ?_⟩
  · intro signs
    obtain ⟨hdisk, _, hsub, hout, hball, _, hFF, hFC, hJC, hDisj⟩ := hSectors signs
    rw [union_assoc] at hdisk hsub hout
    refine ⟨hFF, hDisj.symm, ?_, _, hdisk, hsub, hout, hball⟩
    intro j i x hx
    cases j
    · have hvec : ![signedTubeReindex (eta 0) (signs 0),
          signedTubeReindex (eta 1) (signs 1)] =
        (fun i : Fin 2 => if eta i then signs i else !(signs i)) := by
          funext i
          fin_cases i <;> rfl
      have hxfoot := (hAlignedQuarter (signs 0) (signs 1) x).mp hx
      rw [hvec] at hxfoot
      have hface : (alignedFoot x : E) ∈ face i (localSign i (signs i.rev)) ↔
          (alignedFoot x : E) ∈ footRadius i (localSign i (signs i.rev)) := by
        exact ⟨fun hh => (hFC i).subset ⟨hxfoot, hh⟩,
          fun hh => ((hFC i).superset hh).2⟩
      exact hface.trans (hAlignedRadius i (signs i.rev) x).symm
    · have hxjoint := (hGquarters (signs 0) (signs 1) x).mp hx
      have hface : (G x : E) ∈ face i (localSign i (signs i.rev)) ↔
          (G x : E) ∈ jointRadius i (signs i.rev) := by
        exact ⟨fun hh => (hJC i).subset ⟨hxjoint, hh⟩,
          fun hh => ((hJC i).superset hh).2⟩
      exact hface.trans (hGradii i (signs i.rev) x).symm
  intro i sign
  obtain ⟨map, hmap, hAxisKeep, hEndKeep, hAxisMem, hOuterMem⟩ := hHalfFaces i sign
  refine ⟨map, hmap, hAxisKeep, ?_, hAxisMem, hOuterMem⟩
  intro j x
  cases reverseEnds <;> cases j <;> exact hEndKeep _ x

end PoincareConjecture.M76.Dehn
