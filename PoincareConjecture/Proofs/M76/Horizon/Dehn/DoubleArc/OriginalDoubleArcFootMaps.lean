import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFeet
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondMaps











set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_signed_tube_foot_maps
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
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (p : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source →
      (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hpFr : (g p : X) ∈ frontier R) :
    let V := K.barycentricDualBlock {(p : E)}
    let D := (M reg).barycentricDualBlock {(p : E)}
    let Lp := (V.link p).space
    let Z := V.space ∩ (M arc).space
    let bZ := {z | z ∈ Z ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
    let rad := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let foot := fun signs : Fin 2 → Bool =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    ∃ (C0 : Set V3) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
      (theta : V.space ≃ₜ C0) (a : Fin 2 → Bool → E),
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      (∀ j, L j ≠ 0) ∧ C0 = {x | ∀ j, L j x ≤ 1} ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ Lp ↔ (theta z : V3) ∈ frontier C0) ∧
      (∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ (B (g z) - B (g p)) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ (B (g z) - B (g p)) j)) ∧
      IsFinitePLBallPair ℝ Z bZ ∧
      (∀ (i : Fin 2) (sign : Bool),
        let F := {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
          if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
        let O := {z | z ∈ F ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
        IsFinitePLBallPair P2 F (Z ∪ O) ∧ IsFinitePLBallPair ℝ O bZ) ∧
      (∀ (i : Fin 2) (sign : Bool),
        a i sign ≠ (p : E) ∧ IsFinitePLBallPair ℝ (rad i sign) {(p : E), a i sign} ∧
        rad i sign ∩ Lp = {a i sign} ∧
        B (g (a i sign)) i.castSucc = 0 ∧
        if sign then 0 < B (g (a i sign)) i.rev.castSucc
          else B (g (a i sign)) i.rev.castSucc < 0) ∧
      (∀ i, rad i false ∩ rad i true = {(p : E)}) ∧
      (∀ (eps delta : Bool), rad 0 eps ∩ rad 1 delta = {(p : E)}) ∧
      (∀ signs : Fin 2 → Bool,
        let U := rad 0 (signs 1) ∪ rad 1 (signs 0)
        let O := foot signs ∩ Lp
        IsFinitePLBallPair P2 (foot signs) (O ∪ U) ∧
        IsFinitePLBallPair ℝ U {a 0 (signs 1), a 1 (signs 0)} ∧
        IsFinitePLBallPair ℝ O {a 0 (signs 1), a 1 (signs 0)} ∧
        U ∩ O = {a 0 (signs 1), a 1 (signs 0)} ∧
        ∀ i, foot signs ∩ (M (sheet i)).space = rad i (signs i.rev)) ∧
      (⋃ signs : Fin 2 → Bool, foot signs) = V.space ∩ (M fr).space ∧
      ∃ G : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space), G.IsFinitePL ∧
        ∃ (quarter : ∀ eps delta : Bool, signedTubeQuarter eps delta ≃ₜ foot ![eps, delta])
          (radius : ∀ i sign, signedTubeRadius i sign ≃ₜ rad i sign),
          (∀ eps delta, (quarter eps delta).IsFinitePL) ∧
          (∀ i sign, (radius i sign).IsFinitePL) ∧
          (∀ eps delta (x : signedTubeQuarter eps delta),
            (G ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) =
              quarter eps delta x) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = radius i sign x) ∧
          (∀ eps delta (x : signedTubeDiamond),
            (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ foot ![eps, delta]) ∧
          (∀ i sign (x : signedTubeDiamond),
            (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (radius i sign x : E) = (p : E) ↔ (x : P2) = (0, 0)) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (radius i sign x : E) = a i sign ↔ (x : P2) = signedTubeCorner i sign) ∧
          ∀ eps delta (x : signedTubeQuarter eps delta),
            (x : P2) ∈ signedTubeOuterArc eps delta ↔
              (quarter eps delta x : E) ∈ foot ![eps, delta] ∩ Lp := by
  classical
  let V := K.barycentricDualBlock {(p : E)}
  let Lp := (V.link p).space
  let rad := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let foot := fun signs : Fin 2 → Bool =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
  let Q := fun eps delta : Bool => foot ![eps, delta]
  obtain ⟨C0, L, theta, a, hC, hcv, h0, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hrad, hopposite, hcross, hfeet, hcover⟩ :=
    exists_original_signed_tube_feet hAC hAR S K H g hg hgPL M hMK reg fr arc
      sheet hreg hfr harc hsheet p B hsource hface haxis hsheets hregion hpFr
  have hpK : (p : E) ∈ K.vertices := hMK arc p.property
  have hpstar : (p : E) ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    change {(p : E)} ∈ K.faces ∧ insert (p : E) {(p : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (p : E)), and_self]
      using (show {(p : E)} ∈ K.faces from hpK)
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(p : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨v, hv, hzv⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hvt⟩ := K.exists_original_star_face_of_vertex_dual_face hpK hv
    exact hsource ((K.closedStar p).convexHull_subset_space ht (hvt hzv))
  obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
    (fun h => disjoint_left.mp disjoint_interior_frontier (h (hsource hpstar)) hpFr)
  have hSheet (i : Fin 2) {z : E} (hzV : z ∈ V.space) (hzFr : z ∈ (M fr).space) :
      z ∈ (M (sheet i)).space ↔ B (g z) i.castSucc = 0 := by
    have hz2 := (hfront (g z) (hVB hzV)).mp ((hfr z (hVK hzV)).mp hzFr)
    have hzR : (g z : X) ∈ R := (hhalf (g z) (hVB hzV)).mpr (by rw [hz2])
    rw [hsheet i z (hVK hzV), hsheets i (g z) (hVB hzV)]
    exact and_iff_right hzR
  have hQmem (eps delta : Bool) (z : E) : z ∈ Q eps delta ↔
      z ∈ V.space ∧ z ∈ (M fr).space ∧
      (if eps then 0 ≤ B (g z) 0 else B (g z) 0 ≤ 0) ∧
      (if delta then 0 ≤ B (g z) 1 else B (g z) 1 ≤ 0) := by
    constructor
    · intro hz
      exact ⟨hz.1, hz.2.1, hz.2.2 0, hz.2.2 1⟩
    · rintro ⟨hzV, hzF, h0, h1⟩
      refine ⟨hzV, hzF, ?_⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
  have hQsheet0 (eps delta : Bool) : Q eps delta ∩ (M (sheet 0)).space = rad 0 delta :=
    (hfeet ![eps, delta]).2.2.2.2 0
  have hQsheet1 (eps delta : Bool) : Q eps delta ∩ (M (sheet 1)).space = rad 1 eps :=
    (hfeet ![eps, delta]).2.2.2.2 1
  have hQrad0 (eps delta : Bool) : rad 0 delta ⊆ Q eps delta :=
    fun _ hz => ((hQsheet0 eps delta).superset hz).1
  have hQrad1 (eps delta : Bool) : rad 1 eps ⊆ Q eps delta :=
    fun _ hz => ((hQsheet1 eps delta).superset hz).1
  have hpQ (eps delta : Bool) : (p : E) ∈ Q eps delta :=
    hQrad0 eps delta ((hrad 0 delta).2.1.1 (by simp))
  have hzero (sign : Bool) (x : ℝ)
      (h : if sign then 0 ≤ x else x ≤ 0)
      (hn : if !sign then 0 ≤ x else x ≤ 0) : x = 0 := by
    cases sign <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h hn <;>
      exact le_antisymm (by assumption) (by assumption)
  have hInter (eps delta : Bool) :
      Q eps delta ∩ Q eps (!delta) = rad 1 eps ∧
      Q eps delta ∩ Q (!eps) delta = rad 0 delta ∧
      Q eps delta ∩ Q (!eps) (!delta) = {(p : E)} := by
    refine ⟨?_, ?_, ?_⟩
    · ext z
      constructor
      · rintro ⟨hz, hz'⟩
        apply (hQsheet1 eps delta).subset
        refine ⟨hz, (hSheet 1 hz.1 hz.2.1).mpr ?_⟩
        exact hzero delta _ ((hQmem eps delta z).mp hz).2.2.2
          ((hQmem eps (!delta) z).mp hz').2.2.2
      · intro hz
        exact ⟨hQrad1 eps delta hz, hQrad1 eps (!delta) hz⟩
    · ext z
      constructor
      · rintro ⟨hz, hz'⟩
        apply (hQsheet0 eps delta).subset
        refine ⟨hz, (hSheet 0 hz.1 hz.2.1).mpr ?_⟩
        exact hzero eps _ ((hQmem eps delta z).mp hz).2.2.1
          ((hQmem (!eps) delta z).mp hz').2.2.1
      · intro hz
        exact ⟨hQrad0 eps delta hz, hQrad0 (!eps) delta hz⟩
    · ext z
      constructor
      · rintro ⟨hz, hz'⟩
        have h0 := hzero eps _ ((hQmem eps delta z).mp hz).2.2.1
          ((hQmem (!eps) (!delta) z).mp hz').2.2.1
        have h1 := hzero delta _ ((hQmem eps delta z).mp hz).2.2.2
          ((hQmem (!eps) (!delta) z).mp hz').2.2.2
        exact (hcross delta eps).subset
          ⟨(hQsheet0 eps delta).subset ⟨hz, (hSheet 0 hz.1 hz.2.1).mpr h0⟩,
            (hQsheet1 eps delta).subset ⟨hz, (hSheet 1 hz.1 hz.2.1).mpr h1⟩⟩
      · rintro rfl
        exact ⟨hpQ eps delta, hpQ (!eps) (!delta)⟩
  have hQcover : (⋃ eps, ⋃ delta, Q eps delta) = V.space ∩ (M fr).space := by
    ext z
    constructor
    · intro hz
      obtain ⟨eps, delta, hz⟩ := mem_iUnion.mp hz |>.imp fun _ h => mem_iUnion.mp h
      exact hcover.subset (mem_iUnion.mpr ⟨![eps, delta], hz⟩)
    · intro hz
      obtain ⟨signs, hs⟩ := mem_iUnion.mp (hcover.superset hz)
      refine mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, ?_⟩⟩
      have he : ![signs 0, signs 1] = signs := by ext i; fin_cases i <;> rfl
      simpa only [Q, he] using hs
  have hMaps := exists_signed_diamond_map_on_radii (p : E) a rad Q Lp
    (V.space ∩ (M fr).space) (fun i sign => (hrad i sign).2.1)
    (fun i sign => (hrad i sign).1)
    (fun eps delta => ⟨(hfeet ![eps, delta]).1, (hfeet ![eps, delta]).2.2.1,
      (hfeet ![eps, delta]).2.2.2.1, hcross delta eps⟩) hInter hQcover
  exact ⟨C0, L, theta, a, hC, hcv, h0, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hrad, hopposite, hcross, hfeet, hcover, hMaps⟩

end PoincareConjecture.M76.Dehn
