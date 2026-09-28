import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcFootMaps
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization











set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in


theorem exists_original_endpoint_sector_boundary_disk
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
    let F := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let O := fun i sign => {z | z ∈ F i sign ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
    let rad := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let foot := fun signs : Fin 2 → Bool =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    let sectorBoundary := fun signs : Fin 2 → Bool =>
      {z | z ∈ D.space ∧
        (∀ i : Fin 2, if signs i then 0 ≤ B (g z) i.castSucc
          else B (g z) i.castSucc ≤ 0) ∧
        (z ∈ Lp ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
    ∃ (C0 : Set V3) (theta : V.space ≃ₜ C0) (a : Fin 2 → Bool → E)
      (G : signedTubeDiamond ≃ₜ ↥(V.space ∩ (M fr).space)),
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ Lp ↔ (theta z : V3) ∈ frontier C0) ∧
      (∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ B (g z) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ B (g z) j)) ∧
      IsFinitePLBallPair ℝ Z bZ ∧
      (∀ i sign, IsFinitePLBallPair P2 (F i sign) (Z ∪ O i sign) ∧
        IsFinitePLBallPair ℝ (O i sign) bZ) ∧
      (∀ i sign, a i sign ≠ (p : E) ∧
        IsFinitePLBallPair ℝ (rad i sign) {(p : E), a i sign} ∧
        rad i sign ∩ Lp = {a i sign}) ∧
      (∀ i sign, rad i sign ⊆ D.space) ∧
      G.IsFinitePL ∧
      (∀ eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ foot ![eps, delta]) ∧
      (∀ i sign (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign) ∧
      (∀ i sign (x : signedTubeRadius i sign),
        ((G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = (p : E) ↔
          (x : P2) = (0, 0)) ∧
        ((G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = a i sign ↔
          (x : P2) = signedTubeCorner i sign)) ∧
      (∀ eps delta (x : signedTubeQuarter eps delta),
        (x : P2) ∈ signedTubeOuterArc eps delta ↔
          (G ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
            foot ![eps, delta] ∩ Lp) ∧
      ∀ signs : Fin 2 → Bool,
      let U := rad 0 (signs 1) ∪ rad 1 (signs 0)
      let T := (F 0 (signs 1) ∪ F 1 (signs 0)) ∪ foot signs
      let rim := ((O 0 (signs 1) ∪ O 1 (signs 0)) ∪ ((foot signs ∩ Lp) ∪ U)) \
        (U \ {a 0 (signs 1), a 1 (signs 0)})
      IsFinitePLBallPair P2 T rim ∧
      T ⊆ sectorBoundary signs ∧ (sectorBoundary signs \ T).Nonempty ∧
      F 0 (signs 1) ∩ F 1 (signs 0) = Z ∧
      ∀ i, foot signs ∩ F i (signs i.rev) = rad i (signs i.rev) := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(p : E)}
  let D := (M reg).barycentricDualBlock {(p : E)}
  let Lp := (V.link p).space
  let Z := V.space ∩ (M arc).space
  let bZ := {z | z ∈ Z ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
  let F := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let O := fun i sign => {z | z ∈ F i sign ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
  let rad := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let foot := fun signs : Fin 2 → Bool =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
  obtain ⟨C0, L, theta, a, hC, hcv, h0, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, aRad, hopposite, hcross, hfeet, hcover, hFootMaps⟩ :=
    exists_original_signed_tube_foot_maps hAC hAR S K H g hg hgPL M hMK reg fr arc
      sheet hreg hfr harc hsheet p B hsource hface haxis hsheets hregion hpFr
  obtain ⟨G, hG, quarter, radius, hquarter, hradius, hkeepQ, hkeepR,
    hGquarter, hGradius, hcenter, hcorner, houter⟩ := hFootMaps
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
  have hD : D.space = V.space ∩ (M reg).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(p : E)}).symm
  have hDV : D.space ⊆ V.space := by rw [hD]; exact inter_subset_left
  have hDR {z : E} (hz : z ∈ D.space) : (g z : X) ∈ R :=
    (hreg z (hVK (hDV hz))).mp ((hD.subset hz).2)
  have hcoord (i : Fin 2) {z : E} (hz : z ∈ D.space)
      (hs : z ∈ (M (sheet i)).space) : B (g z) i.castSucc = 0 :=
    ((hsheets i (g z) (hVB (hDV hz))).mp
      ((hsheet i z (hVK (hDV hz))).mp hs)).2
  obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
    (fun h => disjoint_left.mp disjoint_interior_frontier (h (hsource hpstar)) hpFr)
  have hpA : (g p : X) ∈ A :=
    (harc p (K.vertices_subset_space hpK)).mp ((M arc).vertices_subset_space p.property)
  have hBzero : B (g p) = (0 : V3) := by
    have hz := ((haxis (g p) (hsource hpstar)).mp hpA).2
    ext j
    fin_cases j
    · exact hz.1
    · exact hz.2
    · exact (hfront (g p) (hsource hpstar)).mp hpFr
  have hfootD (signs : Fin 2 → Bool) : foot signs ⊆ D.space := by
    intro z hz
    apply hD.superset
    refine ⟨hz.1, (hreg z (hVK hz.1)).mpr ?_⟩
    apply (hhalf (g z) (hVB hz.1)).mpr
    rw [(hfront (g z) (hVB hz.1)).mp ((hfr z (hVK hz.1)).mp hz.2.1)]
  have hZF (i : Fin 2) (sign : Bool) : Z ⊆ F i sign :=
    fun _ hz => (hfaces i sign).1.1 (Or.inl hz)
  have hOZ (i : Fin 2) (sign : Bool) : O i sign ∩ Z = bZ := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hZF i sign h.1, h.2⟩, h.1⟩⟩
  have hradD (i : Fin 2) (sign : Bool) : rad i sign ⊆ D.space := by
    fin_cases i
    · exact (((hfeet ![false, sign]).2.2.2.2 0).symm.subset.trans inter_subset_left).trans
        (hfootD ![false, sign])
    · exact (((hfeet ![sign, false]).2.2.2.2 1).symm.subset.trans inter_subset_left).trans
        (hfootD ![sign, false])
  refine ⟨C0, theta, a, G, hC, hcv, h0, htheta, hthetaInv, hlink,
    (fun j z => by simpa only [hBzero, sub_zero] using hmarks j z), hZ, hfaces,
    (fun i sign => ⟨(aRad i sign).1, (aRad i sign).2.1, (aRad i sign).2.2.1⟩), hradD, hG,
    hGquarter, hGradius, ?_, ?_, ?_⟩
  · intro i sign x
    rw [hkeepR]
    exact ⟨hcenter i sign x, hcorner i sign x⟩
  · intro eps delta x
    rw [hkeepQ]
    exact houter eps delta x
  intro signs
  let U := rad 0 (signs 1) ∪ rad 1 (signs 0)
  have hFF : F 0 (signs 1) ∩ F 1 (signs 0) = Z := by
    ext z
    constructor
    · intro hz
      refine ⟨hDV hz.1.1, (harc z (hVK (hDV hz.1.1))).mpr ?_⟩
      exact (haxis (g z) (hVB (hDV hz.1.1))).mpr
        ⟨hDR hz.1.1, hcoord 0 hz.1.1 hz.1.2.1, hcoord 1 hz.2.1 hz.2.2.1⟩
    · intro hz
      exact ⟨hZF 0 (signs 1) hz, hZF 1 (signs 0) hz⟩
  have hsheetDisk : IsFinitePLBallPair P2 (F 0 (signs 1) ∪ F 1 (signs 0))
      (O 0 (signs 1) ∪ O 1 (signs 0)) := by
    apply IsFinitePLBallPair.union_of_interval_attachment
      (d := Z) (q := bZ)
    · simpa only [union_comm] using (hfaces 0 (signs 1)).1
    · simpa only [union_comm] using (hfaces 1 (signs 0)).1
    · exact (hfaces 0 (signs 1)).2
    · exact (hfaces 1 (signs 0)).2
    · exact hZ
    · exact hOZ 0 (signs 1)
    · exact hOZ 1 (signs 0)
    · exact hFF
  have hradF (i : Fin 2) : rad i (signs i.rev) ⊆ F i (signs i.rev) := by
    intro z hz
    have hf : z ∈ foot signs := ((hfeet signs).2.2.2.2 i).superset hz |>.1
    exact ⟨hfootD signs hf, hz.2.2.1, hz.2.2.2⟩
  have hcontact (i : Fin 2) : foot signs ∩ F i (signs i.rev) = rad i (signs i.rev) := by
    ext z
    exact ⟨fun h => ((hfeet signs).2.2.2.2 i).subset ⟨h.1, h.2.2.1⟩,
      fun h => ⟨(((hfeet signs).2.2.2.2 i).superset h).1, hradF i h⟩⟩
  have hcontact0 : foot signs ∩ F 0 (signs 1) = rad 0 (signs 1) := hcontact 0
  have hcontact1 : foot signs ∩ F 1 (signs 0) = rad 1 (signs 0) := hcontact 1
  have hmeet : (F 0 (signs 1) ∪ F 1 (signs 0)) ∩ foot signs = U := by
    rw [inter_comm, inter_union_distrib_left, hcontact0, hcontact1]
  have hUO : U ⊆ O 0 (signs 1) ∪ O 1 (signs 0) := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl ⟨hradF 0 hz, Or.inr hz.2.1⟩
    · exact Or.inr ⟨hradF 1 hz, Or.inr hz.2.1⟩
  have hends : a 0 (signs 1) ≠ a 1 (signs 0) := by
    intro heq
    have h0rad : a 0 (signs 1) ∈ rad 0 (signs 1) :=
      (aRad 0 (signs 1)).2.1.1 (by simp)
    have h1rad : a 0 (signs 1) ∈ rad 1 (signs 0) := by
      rw [heq]
      exact (aRad 1 (signs 0)).2.1.1 (by simp)
    exact (aRad 0 (signs 1)).1 ((hcross (signs 1) (signs 0)).subset ⟨h0rad, h1rad⟩)
  refine ⟨?_, ?_, ?_, hFF, hcontact⟩
  · exact hsheetDisk.union_of_boundary_interval (hfeet signs).1
      (hfeet signs).2.1 hUO (fun _ h => Or.inr h) hends hmeet
  · intro z hz
    rcases hz with (hz | hz) | hz
    · refine ⟨hz.1, ?_, Or.inr (Or.inr ⟨0, hz.2.1⟩)⟩
      intro i
      fin_cases i
      · have hc := hcoord 0 hz.1 hz.2.1
        change B (g z) 0 = 0 at hc
        change if signs 0 then 0 ≤ B (g z) 0 else B (g z) 0 ≤ 0
        simp only [hc, le_refl, ite_self]
      · exact hz.2.2
    · refine ⟨hz.1, ?_, Or.inr (Or.inr ⟨1, hz.2.1⟩)⟩
      intro i
      fin_cases i
      · exact hz.2.2
      · have hc := hcoord 1 hz.1 hz.2.1
        change B (g z) 1 = 0 at hc
        change if signs 1 then 0 ≤ B (g z) 1 else B (g z) 1 ≤ 0
        simp only [hc, le_refl, ite_self]
    · exact ⟨hfootD signs hz, hz.2.2, Or.inr (Or.inl hz.2.1)⟩
  · let w : V3 := ![if signs 0 then 1 else -1, if signs 1 then 1 else -1, 1]
    have hw : w ≠ 0 := by
      intro h
      have h2 := congrFun h 2
      change (1 : ℝ) = 0 at h2
      exact one_ne_zero h2
    let r := (gauge C0 w)⁻¹
    obtain ⟨hr, hrfront⟩ := hC.gauge_inv_smul_mem_frontier hcv h0 hw
    change 0 < r at hr
    let y := r • w
    have hyC : y ∈ C0 := hC.isClosed.closure_eq ▸ frontier_subset_closure hrfront
    let z : V.space := theta.symm ⟨y, hyC⟩
    have hthetaZ : (theta z : V3) = y := by simp only [z, Homeomorph.apply_symm_apply]
    have hmark (j : Fin 3) :
        (y j = 0 ↔ B (g z) j = 0) ∧ (0 ≤ y j ↔ 0 ≤ B (g z) j) := by
      simpa only [hthetaZ, hBzero, sub_zero] using hmarks j z
    have hpos (j : Fin 3) (hy : 0 < y j) : 0 < B (g z) j := by
      refine lt_of_le_of_ne ((hmark j).2.mp hy.le) ?_
      intro h
      exact hy.ne' ((hmark j).1.mpr h.symm)
    have hneg (j : Fin 3) (hy : y j < 0) : B (g z) j < 0 :=
      lt_of_not_ge (fun h => not_le_of_gt hy ((hmark j).2.mpr h))
    have hwi (i : Fin 2) : w i.castSucc = if signs i then 1 else -1 := by
      fin_cases i <;> rfl
    have hstrict (i : Fin 2) :
        if signs i then 0 < B (g z) i.castSucc else B (g z) i.castSucc < 0 := by
      cases hs : signs i
      · simp only [hs, Bool.false_eq_true, ↓reduceIte]
        apply hneg
        have hn : -r < 0 := by linarith
        simpa only [y, Pi.smul_apply, smul_eq_mul, hwi, hs, Bool.false_eq_true,
          ↓reduceIte, mul_neg, mul_one] using hn
      · simp only [hs, ↓reduceIte]
        apply hpos
        simpa only [y, Pi.smul_apply, smul_eq_mul, hwi, hs, ↓reduceIte, mul_one] using hr
    have hheight : 0 < B (g z) 2 := by
      apply hpos
      change 0 < r * 1
      simpa only [mul_one] using hr
    have hzD : (z : E) ∈ D.space := by
      apply hD.superset
      exact ⟨z.property, (hreg z (hVK z.property)).mpr
        ((hhalf (g z) (hVB z.property)).mpr hheight.le)⟩
    have hweak (i : Fin 2) :
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0 := by
      have h := hstrict i
      cases hs : signs i <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
        exact h.le
    have hzlink : (z : E) ∈ Lp := (hlink z).mpr (hthetaZ.symm ▸ hrfront)
    have hnSheet (i : Fin 2) : (z : E) ∉ (M (sheet i)).space := by
      intro hs
      have hc := hcoord i hzD hs
      have h := hstrict i
      cases hi : signs i <;> simp only [hi, Bool.false_eq_true, ↓reduceIte, hc] at h <;>
        exact (lt_irrefl 0 h)
    have hnFr : (z : E) ∉ (M fr).space := by
      intro hf
      exact hheight.ne' ((hfront (g z) (hVB z.property)).mp
        ((hfr z (hVK z.property)).mp hf))
    refine ⟨z, ⟨hzD, hweak, Or.inl hzlink⟩, ?_⟩
    rintro ((hz | hz) | hz)
    · exact hnSheet 0 hz.2.1
    · exact hnSheet 1 hz.2.1
    · exact hnFr hz.2.1

end PoincareConjecture.M76.Dehn
