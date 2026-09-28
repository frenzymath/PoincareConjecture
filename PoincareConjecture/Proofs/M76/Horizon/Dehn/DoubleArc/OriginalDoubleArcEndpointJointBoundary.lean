import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointSectorBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointRestrictions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointSectorExterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointSectorBalls
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_endpoint_joint_boundary_disk
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
    (hvFr : (g v : X) ∈ frontier R) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let Lp := (V.link v).space
    let J := K.barycentricDualBlock s
    let m := s.centroid ℝ id
    let q := (J.link m).space
    let Z := V.space ∩ (M arc).space
    let bZ := {z | z ∈ Z ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
    let face := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let outer := fun i sign => {z | z ∈ face i sign ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
    let footRadius := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let foot := fun signs : Fin 2 → Bool =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
    ∃ (C0 : Set V3) (theta : V.space ≃ₜ C0)
      (p : (M arc).vertices) (T : Fin 2 → Bool → Finset E)
      (G : signedTubeDiamond ≃ₜ J.space) (eta : Fin 2 → Bool) (b : Fin 2 → Bool → E)
      (footMap : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space)),
      let a := fun i sign => (T i sign).centroid ℝ id
      let rad := fun i sign => segment ℝ m (a i sign)
      let Q := fun eps delta : Bool => {z | z ∈ J.space ∧
        (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
        if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ Lp ↔ (theta z : V3) ∈ frontier C0) ∧
      (∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ B v (g z) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ B v (g z) j)) ∧
      Disjoint J.space (M fr).space ∧ J.space ⊆ V.space ∧
      J.space ∩ (M arc).space = {m} ∧ J.space ⊆ Lp ∧
      (v : E) ≠ m ∧ bZ = {(v : E), m} ∧
      IsFinitePLBallPair ℝ Z bZ ∧
      (∀ i sign, IsFinitePLBallPair P2 (face i sign) (Z ∪ outer i sign) ∧
        IsFinitePLBallPair ℝ (outer i sign) bZ) ∧
      (∀ i sign, b i sign ≠ (v : E) ∧
        IsFinitePLBallPair ℝ (footRadius i sign) {(v : E), b i sign} ∧
        footRadius i sign ∩ Lp = {b i sign}) ∧
      (∀ i sign, footRadius i sign ⊆ D.space) ∧
      (∀ i sign,
        let localSign := signedTubeReindex (eta i.rev) sign
        IsFinitePLBallPair ℝ (rad i sign) {m, a i sign} ∧
        rad i sign ⊆ outer i localSign ∧
        footRadius i localSign ⊆ outer i localSign ∧
        Disjoint (footRadius i localSign) (rad i sign) ∧
        Z ∩ outer i localSign = {(v : E), m} ∧ a i sign ≠ m ∧ rad i sign ⊆ J.space) ∧
      G.IsFinitePL ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q eps delta) ∧
      (∀ i sign (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign) ∧
      (G ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = m ∧
      (∀ i sign,
        (G ⟨signedTubeCorner i sign,
          signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E) = a i sign) ∧
      footMap.IsFinitePL ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔ (footMap x : E) ∈ foot ![eps, delta]) ∧
      (∀ i sign (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeRadius i sign ↔ (footMap x : E) ∈ footRadius i sign) ∧
      (∀ i sign (x : signedTubeRadius i sign),
        ((footMap ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = (v : E) ↔
          (x : P2) = (0, 0)) ∧
        ((footMap ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = b i sign ↔
          (x : P2) = signedTubeCorner i sign)) ∧
      (∀ eps delta (x : signedTubeQuarter eps delta),
        (x : P2) ∈ signedTubeOuterArc eps delta ↔
          (footMap ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
            foot ![eps, delta] ∩ Lp) ∧
      ((signedTubeDiamondReflection eta).trans footMap).IsFinitePL ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔
          ((signedTubeDiamondReflection eta).trans footMap x : E) ∈
            foot ![signedTubeReindex (eta 0) eps, signedTubeReindex (eta 1) delta]) ∧
      (∀ i sign (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeRadius i sign ↔
          ((signedTubeDiamondReflection eta).trans footMap x : E) ∈
            footRadius i (signedTubeReindex (eta i.rev) sign)) ∧
      ∀ signs : Fin 2 → Bool,
        let localSigns := fun i => if eta i then signs i else !(signs i)
        let Ufoot := footRadius 0 (localSigns 1) ∪ footRadius 1 (localSigns 0)
        let three := (face 0 (localSigns 1) ∪ face 1 (localSigns 0)) ∪ foot localSigns
        let rim := ((outer 0 (localSigns 1) ∪ outer 1 (localSigns 0)) ∪
          ((foot localSigns ∩ Lp) ∪ Ufoot)) \ (Ufoot \ {b 0 (localSigns 1), b 1 (localSigns 0)})
        let Ujoint := rad 0 (signs 1) ∪ rad 1 (signs 0)
        let Qj := Q (signs 0) (signs 1)
        let fullRim := (rim ∪ ((Qj ∩ q) ∪ Ujoint)) \ (Ujoint \ {a 0 (signs 1), a 1 (signs 0)})
        let sectorBoundary := {z | z ∈ D.space ∧
          (∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc
            else B v (g z) i.castSucc ≤ 0) ∧
          (z ∈ Lp ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
        IsFinitePLBallPair P2 (three ∪ Qj) fullRim ∧
        three ∩ Qj = Ujoint ∧ three ∪ Qj ⊆ sectorBoundary ∧
        (sectorBoundary \ (three ∪ Qj)).Nonempty ∧
        IsFinitePLBallPair V3
          (D.space ∩ {z | ∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc
            else B v (g z) i.castSucc ≤ 0}) sectorBoundary ∧
        IsFinitePLBallPair P2 (sectorBoundary \ ((three ∪ Qj) \ fullRim)) fullRim ∧
        face 0 (localSigns 1) ∩ face 1 (localSigns 0) = Z ∧
        (∀ i, foot localSigns ∩ face i (localSigns i.rev) = footRadius i (localSigns i.rev)) ∧
        (∀ i, Qj ∩ face i (localSigns i.rev) = rad i (signs i.rev)) ∧
        Disjoint Qj (foot localSigns) := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let Lp := (V.link v).space
  let J := K.barycentricDualBlock s
  let m := s.centroid ℝ id
  let q := (J.link m).space
  let face := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let outer := fun i sign => {z | z ∈ face i sign ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
  let footRadius := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let foot := fun signs : Fin 2 → Bool =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
  obtain ⟨p, T, G, hG, hps, hGquarters, hGradii, hGsheets, hGcenter,
    hGcorners, hGquarterMaps, hGradiusMaps, hJreg, hmiss, hJarc, hlinks, hANe,
    hQuarter, hchange⟩ := exists_original_signed_tube_joint_restrictions
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB s hs hcard
  obtain ⟨eta, hetaEnds, heta⟩ := hchange v hvs
  obtain ⟨C0, theta, b, footMap, hC, hcv, hzero, htheta, hthetaInv, hlink, hmarks,
    hZ, hfaces, hFootGeometry, hFootRegion, hFoot, hFootQuarter, hFootRadius, hFootEnds,
    hFootOuter, hb⟩ :=
    exists_original_endpoint_sector_boundary_disk
    hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet
    v (B v) (hB v).1 (hB v).2.1 (hB v).2.2.1 (hB v).2.2.2 hregion hvFr
  let a : Fin 2 → Bool → E := fun i sign => (T i sign).centroid ℝ id
  let rad := fun i sign => segment ℝ m (a i sign)
  let Q := fun eps delta : Bool => {z | z ∈ J.space ∧
    (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
    if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
  have hJD : J.space ⊆ D.space := by
    rw [hJreg]
    exact space_subset_of_le ((M reg).barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hvs))
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hvV : (v : E) ∈ V.space := by
    have h := V.vertices_subset_space (K.faceCentroid_mem_barycentricDualBlock_vertices hvK)
    simpa only [Finset.centroid_singleton, id_eq] using h
  have hvArc : (v : E) ∈ (M arc).space := (M arc).vertices_subset_space v.property
  have hvFront : (v : E) ∈ (M fr).space :=
    (hfr v (K.vertices_subset_space hvK)).mpr hvFr
  have hmBoth : m ∈ J.space ∩ (M arc).space := hJarc.superset rfl
  have hJV : J.space ⊆ V.space := space_subset_of_le
    (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hvs))
  have hvm : (v : E) ≠ m := fun heq =>
    disjoint_left.mp hmiss (heq ▸ hmBoth.1) hvFront
  have hZboundary : {z | z ∈ V.space ∩ (M arc).space ∧
      (z ∈ Lp ∨ z ∈ (M fr).space)} = {(v : E), m} := by
    obtain ⟨x, y, hxy, hpair⟩ := hZ.exists_boundary_eq_pair
    have hv : (v : E) ∈ ({x, y} : Set E) :=
      hpair.subset ⟨⟨hvV, hvArc⟩, Or.inr hvFront⟩
    have hm : m ∈ ({x, y} : Set E) :=
      hpair.subset ⟨⟨hJV hmBoth.1, hmBoth.2⟩, Or.inl (hlinks v hvs hmBoth.1)⟩
    rw [hpair]
    rcases hv with hv | hv <;> rcases hm with hm | hm
    · exact False.elim (hvm (hv.trans hm.symm))
    · simp only [hv, show m = y from hm]
    · rw [hv, show m = x from hm, pair_comm]
    · exact False.elim (hvm (hv.trans hm.symm))
  have hJointRadiusData (i : Fin 2) (sign : Bool) :
      rad i sign ⊆ J.space ∩ (M (sheet i)).space ∧
      ∀ z ∈ rad i sign,
        if sign then 0 ≤ B p (g z) i.rev.castSucc else B p (g z) i.rev.castSucc ≤ 0 := by
    fin_cases i
    · have h := (hQuarter false sign).2.2.2.2.1
      exact ⟨fun z hz => ⟨(h.symm.subset hz).1.1, (h.symm.subset hz).2⟩,
        fun z hz => (h.symm.subset hz).1.2.2⟩
    · have h := (hQuarter sign false).2.2.2.2.2.1
      exact ⟨fun z hz => ⟨(h.symm.subset hz).1.1, (h.symm.subset hz).2⟩,
        fun z hz => (h.symm.subset hz).1.2.1⟩
  have hJointOuter (i : Fin 2) (sign : Bool) :
      rad i sign ⊆ outer i (signedTubeReindex (eta i.rev) sign) := by
    intro z hz
    have hj := (hJointRadiusData i sign).1 hz
    exact ⟨⟨hJD hj.1, hj.2, (heta i.rev sign z hj.1).mp ((hJointRadiusData i sign).2 z hz)⟩,
      Or.inl (hlinks v hvs hj.1)⟩
  have hFootOuterGeometry (i : Fin 2) (sign : Bool) : footRadius i sign ⊆ outer i sign :=
    fun z hz => ⟨⟨hFootRegion i sign hz, hz.2.2.1, hz.2.2.2⟩, Or.inr hz.2.1⟩
  have hOuterAxis (i : Fin 2) (sign : Bool) :
      (V.space ∩ (M arc).space) ∩ outer i sign = {(v : E), m} := by
    rw [← hZboundary]
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, hz.2.2⟩
    · intro hz
      exact ⟨hz.1, (hfaces i sign).1.1 (Or.inl hz.1), hz.2⟩
  refine ⟨C0, theta, p, T, G, eta, b, footMap, hC, hcv, hzero, htheta, hthetaInv,
    hlink, hmarks, hmiss,
    space_subset_of_le (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hvs)),
    hJarc, hlinks v hvs, hvm, hZboundary, hZ, hfaces, hFootGeometry, hFootRegion, ?_,
    hG, hGquarters, hGradii, hGcenter, hGcorners,
    hFoot, hFootQuarter, hFootRadius, hFootEnds, hFootOuter,
    signedTubeDiamondReflection_trans_isFinitePL hFoot eta,
    signedTubeDiamondReflection_trans_quarter footMap (fun eps delta => foot ![eps, delta])
      hFootQuarter eta,
    signedTubeDiamondReflection_trans_radius footMap footRadius hFootRadius eta, ?_⟩
  · intro i sign
    refine ⟨?_, hJointOuter i sign, hFootOuterGeometry i _, ?_, hOuterAxis i _, hANe i sign,
      (hJointRadiusData i sign).1.trans inter_subset_left⟩
    · have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).affine_image
        (ContinuousAffineMap.lineMap m (a i sign))
        (AffineMap.lineMap_injective ℝ (hANe i sign).symm).injOn
      change IsFinitePLBallPair ℝ
        ((AffineMap.lineMap m (a i sign)) '' Icc (0 : ℝ) 1)
        ((AffineMap.lineMap m (a i sign)) '' ({0, 1} : Set ℝ)) at h
      rw [← segment_eq_image_lineMap, image_pair, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] at h
      exact h
    · exact disjoint_left.mpr (fun z hf hj => disjoint_left.mp hmiss
        ((hJointRadiusData i sign).1 hj).1 hf.2.1)
  intro signs
  let localSigns := fun i => if eta i then signs i else !(signs i)
  let Ufoot := footRadius 0 (localSigns 1) ∪ footRadius 1 (localSigns 0)
  let three := (face 0 (localSigns 1) ∪ face 1 (localSigns 0)) ∪ foot localSigns
  let rim := ((outer 0 (localSigns 1) ∪ outer 1 (localSigns 0)) ∪
    ((foot localSigns ∩ Lp) ∪ Ufoot)) \ (Ufoot \ {b 0 (localSigns 1), b 1 (localSigns 0)})
  let Ujoint := rad 0 (signs 1) ∪ rad 1 (signs 0)
  let Qj := Q (signs 0) (signs 1)
  have hQside {z : E} (hz : z ∈ Qj) (i : Fin 2) :
      if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0 := by
    apply (heta i (signs i) z hz.1).mp
    fin_cases i
    · exact hz.2.1
    · exact hz.2.2
  have hradQ (i : Fin 2) : rad i (signs i.rev) ⊆ Qj := by
    fin_cases i
    · exact fun _ hz => ((hQuarter (signs 0) (signs 1)).2.2.2.2.1.superset hz).1
    · exact fun _ hz => ((hQuarter (signs 0) (signs 1)).2.2.2.2.2.1.superset hz).1
  have hradSheet (i : Fin 2) : rad i (signs i.rev) ⊆ (M (sheet i)).space := by
    fin_cases i
    · exact fun _ hz => ((hQuarter (signs 0) (signs 1)).2.2.2.2.1.superset hz).2
    · exact fun _ hz => ((hQuarter (signs 0) (signs 1)).2.2.2.2.2.1.superset hz).2
  have hradFace (i : Fin 2) : rad i (signs i.rev) ⊆ face i (localSigns i.rev) := by
    intro z hz
    exact ⟨hJD (hradQ i hz).1, hradSheet i hz, hQside (hradQ i hz) i.rev⟩
  have hQcontact0 : Qj ∩ face 0 (localSigns 1) = rad 0 (signs 1) := by
    ext z
    exact ⟨fun h => (hQuarter (signs 0) (signs 1)).2.2.2.2.1.subset ⟨h.1, h.2.2.1⟩,
      fun h => ⟨hradQ 0 h, hradFace 0 h⟩⟩
  have hQcontact1 : Qj ∩ face 1 (localSigns 0) = rad 1 (signs 0) := by
    ext z
    exact ⟨fun h => (hQuarter (signs 0) (signs 1)).2.2.2.2.2.1.subset ⟨h.1, h.2.2.1⟩,
      fun h => ⟨hradQ 1 h, hradFace 1 h⟩⟩
  have hQfoot : Disjoint Qj (foot localSigns) := disjoint_left.mpr
    (fun z hz hf => disjoint_left.mp hmiss hz.1 hf.2.1)
  have hmeet : three ∩ Qj = Ujoint := by
    ext z
    constructor
    · rintro ⟨(hz | hz) | hz, hq⟩
      · exact Or.inl (hQcontact0.subset ⟨hq, hz⟩)
      · exact Or.inr (hQcontact1.subset ⟨hq, hz⟩)
      · exact (disjoint_left.mp hQfoot hq hz).elim
    · rintro (hz | hz)
      · exact ⟨Or.inl (Or.inl (hradFace 0 hz)), hradQ 0 hz⟩
      · exact ⟨Or.inl (Or.inr (hradFace 1 hz)), hradQ 1 hz⟩
  have hUQ : Ujoint ⊆ Qj := fun _ hz => hz.elim (fun h => hradQ 0 h) (fun h => hradQ 1 h)
  have hUouter : Ujoint ⊆ outer 0 (localSigns 1) ∪ outer 1 (localSigns 0) := by
    intro z hz
    have hl : z ∈ Lp := hlinks v hvs (hUQ hz).1
    rcases hz with hz | hz
    · exact Or.inl ⟨hradFace 0 hz, Or.inl hl⟩
    · exact Or.inr ⟨hradFace 1 hz, Or.inl hl⟩
  have hUrim : Ujoint ⊆ rim := by
    intro z hz
    refine ⟨Or.inl (hUouter hz), ?_⟩
    rintro ⟨huf, _⟩
    have hf : z ∈ (M fr).space := huf.elim (fun h => h.2.1) (fun h => h.2.1)
    exact disjoint_left.mp hmiss (hUQ hz).1 hf
  have hends : a 0 (signs 1) ≠ a 1 (signs 0) := by
    intro heq
    have h0 : a 0 (signs 1) ∈ rad 0 (signs 1) := right_mem_segment ℝ _ _
    have h1 : a 0 (signs 1) ∈ rad 1 (signs 0) := heq ▸ right_mem_segment ℝ _ _
    exact hANe 0 (signs 1)
      ((hQuarter (signs 0) (signs 1)).2.2.2.2.2.2.subset ⟨h0, h1⟩)
  let fullRim := (rim ∪ ((Qj ∩ q) ∪ Ujoint)) \ (Ujoint \ {a 0 (signs 1), a 1 (signs 0)})
  let sectorBoundary := {z | z ∈ D.space ∧
    (∀ i : Fin 2, if localSigns i then 0 ≤ B v (g z) i.castSucc
      else B v (g z) i.castSucc ≤ 0) ∧
    (z ∈ Lp ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
  have hfullDisk : IsFinitePLBallPair P2 (three ∪ Qj) fullRim :=
    (hb localSigns).1.union_of_boundary_interval
    (hQuarter (signs 0) (signs 1)).1 (hQuarter (signs 0) (signs 1)).2.1
      hUrim (fun _ hz => Or.inr hz) hends hmeet
  have hfullSub : three ∪ Qj ⊆ sectorBoundary := by
    intro z hz
    rcases hz with hz | hz
    · exact (hb localSigns).2.1 hz
    · exact ⟨hJD hz.1, hQside hz, Or.inl (hlinks v hvs hz.1)⟩
  have hfullOut : (sectorBoundary \ (three ∪ Qj)).Nonempty := by
    obtain ⟨z, hzD, hzlink, hzJ, hzfr, hzsheets, hzstrict⟩ :=
      exists_original_endpoint_sector_exterior_point K M hMK reg fr arc sheet
        (fun z => (g z : X)) R S hreg hfr hsheet v (B v) (hB v).1 (hB v).2.2.2
        hregion hvFr C0 theta hC hcv hzero hlink hmarks J.space
        (J.isCompact_space_of_finite (K.barycentricDualBlock_finite s))
        (space_subset_of_le (K.barycentricDualBlock_antitone
          (Finset.singleton_subset_iff.mpr hvs))) hJD hmiss localSigns
    have hzweak (i : Fin 2) :
        if localSigns i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0 := by
      have hi := hzstrict i
      cases hs : localSigns i <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hi ⊢ <;>
        exact hi.le
    refine ⟨z, ⟨hzD, hzweak, Or.inl hzlink⟩, ?_⟩
    rintro (((hz | hz) | hz) | hz)
    · exact hzsheets 0 hz.2.1
    · exact hzsheets 1 hz.2.1
    · exact hzfr hz.2.1
    · exact hzJ hz.1
  have hball := isFinitePLBallPair_original_endpoint_sector hAC S K H g hg M hMK
    reg fr arc sheet hreg hfr harc hsheet v (B v) (hB v).1 (hB v).2.1
    (hB v).2.2.1 (hB v).2.2.2 hregion hvFr localSigns
  refine ⟨hfullDisk, hmeet, hfullSub, hfullOut, hball,
    hball.boundary_disk_complement (by simp) hfullDisk hfullSub hfullOut,
    (hb localSigns).2.2.2.1, (hb localSigns).2.2.2.2, ?_, hQfoot⟩
  intro i
  fin_cases i
  · exact hQcontact0
  · exact hQcontact1

end PoincareConjecture.M76.Dehn
