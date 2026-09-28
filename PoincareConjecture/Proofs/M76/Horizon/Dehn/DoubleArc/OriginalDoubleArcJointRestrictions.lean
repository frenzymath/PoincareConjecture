import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointMaps

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_signed_tube_joint_restrictions
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
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2) :
    let J := K.barycentricDualBlock s
    let m := s.centroid ℝ id
    let q := (J.link m).space
    let I := fun i : Fin 2 => ((M (sheet i)).barycentricDualBlock s).space
    ∃ (p : (M arc).vertices) (T : Fin 2 → Bool → Finset E),
      let a := fun i sign => (T i sign).centroid ℝ id
      let rad := fun i sign => segment ℝ m (a i sign)
      let Q := fun eps delta : Bool => {z | z ∈ J.space ∧
        (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
        if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
      ∃ G : signedTubeDiamond ≃ₜ J.space, G.IsFinitePL ∧
        (p : E) ∈ s ∧
        (∀ eps delta (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q eps delta) ∧
        (∀ i sign (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign) ∧
        (∀ i (x : signedTubeDiamond), (x : P2) ∈ signedTubeSheet i ↔ (G x : E) ∈ I i) ∧
        (G ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = m ∧
        (∀ i sign,
          (G ⟨signedTubeCorner i sign,
            signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E) = a i sign) ∧
        (∀ eps delta, ∃ quarter : signedTubeQuarter eps delta ≃ₜ Q eps delta,
          quarter.IsFinitePL ∧ ∀ x : signedTubeQuarter eps delta,
            (G ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) = quarter x) ∧
        (∀ i sign, ∃ radius : signedTubeRadius i sign ≃ₜ rad i sign,
          radius.IsFinitePL ∧ ∀ x : signedTubeRadius i sign,
            (G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = radius x) ∧
        J.space = ((M reg).barycentricDualBlock s).space ∧
        Disjoint J.space (M fr).space ∧ J.space ∩ (M arc).space = {m} ∧
        (∀ v ∈ s, J.space ⊆ ((K.barycentricDualBlock {v}).link v).space) ∧
        (∀ i sign, a i sign ≠ m) ∧
        (∀ eps delta : Bool,
          let U := rad 0 delta ∪ rad 1 eps
          let O := Q eps delta ∩ q
          IsFinitePLBallPair P2 (Q eps delta) (O ∪ U) ∧
          IsFinitePLBallPair ℝ U {a 0 delta, a 1 eps} ∧
          IsFinitePLBallPair ℝ O {a 0 delta, a 1 eps} ∧
          U ∩ O = {a 0 delta, a 1 eps} ∧
          Q eps delta ∩ (M (sheet 0)).space = rad 0 delta ∧
          Q eps delta ∩ (M (sheet 1)).space = rad 1 eps ∧
          rad 0 delta ∩ rad 1 eps = {m}) ∧
        ∀ v : (M arc).vertices, (v : E) ∈ s → ∃ eta : Fin 2 → Bool,
          (∀ i : Fin 2,
            if eta i then
              B v (g (a i.rev false)) i.castSucc < 0 ∧
                0 < B v (g (a i.rev true)) i.castSucc
            else
              0 < B v (g (a i.rev false)) i.castSucc ∧
                B v (g (a i.rev true)) i.castSucc < 0) ∧
          ∀ (i : Fin 2) (sign : Bool) z, z ∈ J.space →
            ((if sign then 0 ≤ B p (g z) i.castSucc else B p (g z) i.castSucc ≤ 0) ↔
              if (if eta i then sign else !sign) then 0 ≤ B v (g z) i.castSucc
                else B v (g z) i.castSucc ≤ 0) := by
  classical
  let J := K.barycentricDualBlock s
  let m := s.centroid ℝ id
  obtain ⟨p, T, G, hG, _, _, hSheets, hCenter, hRad0, hRad1, hps,
    quarter, radius, hQuarter, hRadius, hKeepQuarter, hKeepRadius, hRadiusCenter, hRadiusEnd,
    hJreg, hmiss, hJarc, hlinks, hANe, hQuarterGeometry, hchange⟩ :=
    exists_original_signed_tube_joint_boundary_maps
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB s hs hcard
  let a : Fin 2 → Bool → E := fun i sign => (T i sign).centroid ℝ id
  let rad : Fin 2 → Bool → Set E := fun i sign => segment ℝ m (a i sign)
  let Q : Bool → Bool → Set E := fun eps delta =>
    {z | z ∈ J.space ∧
      (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
      if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
  have hRadSubset (i : Fin 2) (sign : Bool) : rad i sign ⊆ J.space := by
    fin_cases i
    · intro z hz
      exact ((hRad0 false sign).symm.subset hz).1.1
    · intro z hz
      exact ((hRad1 sign false).symm.subset hz).1.1
  have hWholeQuarter (eps delta : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q eps delta :=
    G.mem_subset_iff_of_extension (quarter eps delta)
      (fun _ hx => mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx⟩⟩)
      (fun _ hz => hz.1)
      (fun z => Subtype.ext (hKeepQuarter eps delta z)) x
  have hWholeRadius (i : Fin 2) (sign : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign :=
    G.mem_subset_iff_of_extension (radius i sign) (signedTubeRadius_subset_diamond i sign)
      (hRadSubset i sign) (fun z => Subtype.ext (hKeepRadius i sign z)) x
  refine ⟨p, T, G, hG, hps, hWholeQuarter, hWholeRadius, hSheets, hCenter, ?_, ?_, ?_,
    hJreg, hmiss, hJarc, hlinks, hANe, hQuarterGeometry, hchange⟩
  · intro i sign
    exact (hKeepRadius i sign ⟨signedTubeCorner i sign, right_mem_segment ℝ _ _⟩).trans
      ((hRadiusEnd i sign ⟨signedTubeCorner i sign, right_mem_segment ℝ _ _⟩).mpr rfl)
  · intro eps delta
    exact ⟨quarter eps delta, hQuarter eps delta, hKeepQuarter eps delta⟩
  · intro i sign
    exact ⟨radius i sign, hRadius i sign, hKeepRadius i sign⟩

end PoincareConjecture.M76.Dehn
