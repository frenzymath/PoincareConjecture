import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJoints
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricEdgeLabels
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_signed_tube_joint_quarters
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
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
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
      (p : E) ∈ s ∧ (g p : X) ∈ interior R ∧
      IsFinitePLBallPair P2 J.space q ∧
      MapsTo (fun z => (g z : X)) J.space (interior R) ∧
      J.space = ((M reg).barycentricDualBlock s).space ∧
      Disjoint J.space (M fr).space ∧ J.space ∩ (M arc).space = {m} ∧
      (∀ v ∈ s, J.space ⊆ ((K.barycentricDualBlock {v}).link v).space) ∧
      I 0 ∩ I 1 = {m} ∧
      (∀ i : Fin 2,
        I i = J.space ∩ (M (sheet i)).space ∧
        IsFinitePLBallPair ℝ (I i) {a i false, a i true} ∧
        I i = rad i false ∪ rad i true ∧
        (∀ v ∈ (M (sheet i)).faces, s ⊆ v → v.card = 3 →
          v = T i false ∨ v = T i true) ∧
        ∀ sign : Bool,
          T i sign ∈ (M (sheet i)).faces ∧ s ⊆ T i sign ∧ (T i sign).card = 3 ∧
          a i sign ≠ m ∧ IsFinitePLBallPair ℝ (rad i sign) {m, a i sign} ∧
          rad i sign ∩ q = {a i sign} ∧
          rad i sign = I i ∩ {z | if sign then 0 ≤ B p (g z) i.rev.castSucc
            else B p (g z) i.rev.castSucc ≤ 0} ∧
          if sign then 0 < B p (g (a i sign)) i.rev.castSucc
            else B p (g (a i sign)) i.rev.castSucc < 0) ∧
      (∀ eps delta : Bool,
        let U := rad 0 delta ∪ rad 1 eps
        let O := Q eps delta ∩ q
        IsFinitePLBallPair P2 (Q eps delta) (O ∪ U) ∧
        IsFinitePLBallPair ℝ U {a 0 delta, a 1 eps} ∧
        IsFinitePLBallPair ℝ O {a 0 delta, a 1 eps} ∧ U ∩ O = {a 0 delta, a 1 eps} ∧
        Q eps delta ∩ (M (sheet 0)).space = rad 0 delta ∧
        Q eps delta ∩ (M (sheet 1)).space = rad 1 eps ∧
        rad 0 delta ∩ rad 1 eps = {m}) ∧
      (∀ eps delta : Bool,
        Q eps delta ∩ Q eps (!delta) = rad 1 eps ∧
        Q eps delta ∩ Q (!eps) delta = rad 0 delta ∧
        Q eps delta ∩ Q (!eps) (!delta) = {m}) ∧
      (⋃ eps : Bool, ⋃ delta : Bool, Q eps delta) = J.space ∧
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
  let q := (J.link m).space
  let I := fun i : Fin 2 => ((M (sheet i)).barycentricDualBlock s).space
  obtain ⟨p, hps, hpR, hJ, hJR, hJreg, hmiss, hJarc, hlinks, t, u, ht⟩ :=
    exists_original_signed_tube_joint_intervals hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard
  let T : Fin 2 → Bool → Finset E := fun i sign => if sign then u i else t i
  let a : Fin 2 → Bool → E := fun i sign => (T i sign).centroid ℝ id
  let rad : Fin 2 → Bool → Set E := fun i sign => segment ℝ m (a i sign)
  let lam : Fin 2 → E → ℝ := fun i z => B p (g z) i.castSucc
  let side : Bool → ℝ → Prop := fun sign x => if sign then 0 ≤ x else x ≤ 0
  let Q : Bool → Bool → Set E := fun eps delta =>
    {z | z ∈ J.space ∧ side eps (lam 0 z) ∧ side delta (lam 1 z)}
  have hJK : J.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le s)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hpK : (p : E) ∈ K.vertices := hMK arc p.property
  have hJstar : J.space ⊆ (K.closedStar p).space := by
    intro z hz
    have hV := space_subset_of_le (K.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hps)) hz
    obtain ⟨v, hv, hzv⟩ := mem_space_iff.mp hV
    obtain ⟨w, hw, hvw⟩ := K.exists_original_star_face_of_vertex_dual_face hpK hv
    exact (K.closedStar p).convexHull_subset_space hw (hvw hzv)
  have hcont (i : Fin 2) : ContinuousOn (lam i) J.space :=
    (continuous_apply i.castSucc).comp_continuousOn
      ((B p).continuousOn.comp (hgPL.continuousOn.mono hJK)
        (fun _ hz => (hB p).1 (hJstar hz)))
  have hIs (i : Fin 2) : I i = J.space ∩ (M (sheet i)).space := by
    obtain ⟨_, _, _, _, _, _, _, _, hIs, _⟩ := ht i
    exact hIs
  have hIball (i : Fin 2) : IsFinitePLBallPair ℝ (I i) {a i false, a i true} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hI, _⟩ := ht i
    exact hI
  have hmI (i : Fin 2) : m ∈ I i \ {a i false, a i true} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hm, _⟩ := ht i
    exact hm
  have hIq (i : Fin 2) : I i ∩ q = {a i false, a i true} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, heq, _⟩ := ht i
    exact heq
  have hzero (i : Fin 2) : J.space ∩ {z | lam i z = 0} = I i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, heq, _⟩ := ht i
    exact heq
  have hqzero (i : Fin 2) : q ∩ {z | lam i z = 0} = {a i false, a i true} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, heq, _⟩ := ht i
    exact heq
  have hstrict (i : Fin 2) (sign : Bool) :
      if sign then 0 < lam i.rev (a i sign) else lam i.rev (a i sign) < 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, hp⟩ := ht i
    cases sign
    · exact hn
    · exact hp
  have hcoface (i : Fin 2) (sign : Bool) :
      T i sign ∈ (M (sheet i)).faces ∧ s ⊆ T i sign ∧ (T i sign).card = 3 := by
    obtain ⟨htf, huf, hst, hsu, htc, huc, _⟩ := ht i
    cases sign
    · exact ⟨htf, hst, htc⟩
    · exact ⟨huf, hsu, huc⟩
  have hISub (i : Fin 2) : I i ⊆ J.space := (hIs i).subset.trans inter_subset_left
  have hmzero (i : Fin 2) : lam i m = 0 := ((hzero i).symm.subset (hmI i).1).2
  have hcrossI : I 0 ∩ I 1 = {m} := by
    apply Subset.antisymm
    · intro z hz
      have hz0 := (hzero 0).symm.subset hz.1
      have hz1 := (hzero 1).symm.subset hz.2
      exact hJarc.subset ⟨hz0.1, (harc z (hJK hz0.1)).mpr
        (((hB p).2.2.1 (g z) ((hB p).1 (hJstar hz0.1))).mpr
          ⟨interior_subset (hJR hz0.1), hz0.2, hz1.2⟩)⟩
    · rintro z rfl
      exact ⟨(hmI 0).1, (hmI 1).1⟩
  have hane (i : Fin 2) (sign : Bool) : a i sign ≠ m := by
    intro he
    apply (hmI i).2
    cases sign
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  have hab (i : Fin 2) : a i false ≠ a i true := by
    intro he
    have hn := hstrict i false
    have hp := hstrict i true
    change lam i.rev (a i false) < 0 at hn
    change 0 < lam i.rev (a i true) at hp
    rw [he] at hn
    exact (not_lt_of_gt hp) hn
  have haq (i : Fin 2) (sign : Bool) : a i sign ∈ q := by
    apply ((hIq i).symm.subset ?_).2
    cases sign
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hRsub (i : Fin 2) (sign : Bool) : rad i sign ⊆ I i := by
    let N := M (sheet i)
    obtain ⟨hTf, hsT, _⟩ := hcoface i sign
    have hsN : s ∈ N.faces := N.down_closed hTf hsT ((M arc).nonempty_of_mem_faces hs)
    have hedge : ({m, a i sign} : Finset E) ∈ (N.barycentricDualBlock s).faces := by
      refine ⟨(N.barycentric_centroid_pair_face_iff ⟨s, hsN⟩ ⟨T i sign, hTf⟩).mpr
        (Or.inl hsT), ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · exact ⟨s, hsN, Subset.rfl, hz.symm⟩
      · exact ⟨T i sign, hTf, hsT, (Finset.mem_singleton.mp hz).symm⟩
    simpa only [Finset.coe_pair, convexHull_pair] using
      (N.barycentricDualBlock s).convexHull_subset_space hedge
  have hRball (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (rad i sign) {m, a i sign} := by
    have hb := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).affine_image
      (ContinuousAffineMap.lineMap m (a i sign))
      (AffineMap.lineMap_injective ℝ (hane i sign).symm).injOn
    change IsFinitePLBallPair ℝ ((AffineMap.lineMap m (a i sign)) '' Icc (0 : ℝ) 1)
      ((AffineMap.lineMap m (a i sign)) '' ({0, 1} : Set ℝ)) at hb
    rw [← segment_eq_image_lineMap, image_pair, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] at hb
    exact hb
  have hmR (i : Fin 2) (sign : Bool) : m ∈ rad i sign := left_mem_segment ℝ _ _
  have haR (i : Fin 2) (sign : Bool) : a i sign ∈ rad i sign := right_mem_segment ℝ _ _
  have hRzero (i : Fin 2) (sign : Bool) :
      rad i sign ∩ {z | lam i.rev z = 0} ⊆ ({m} : Set E) := by
    intro z hz
    have hzI := hRsub i sign hz.1
    have hzr := (hzero i.rev).subset ⟨hISub i hzI, hz.2⟩
    fin_cases i
    · exact hcrossI.subset ⟨hzI, hzr⟩
    · exact hcrossI.subset ⟨hzr, hzI⟩
  have hRside (i : Fin 2) (sign : Bool) :
      ∀ z ∈ rad i sign, side sign (lam i.rev z) := by
    have hz : rad i sign ∩ {z | lam i.rev z = 0} ⊆ {m, a i sign} :=
      fun z hz => Or.inl (hRzero i sign hz)
    cases sign
    · exact (hRball i false).mapsTo_nonpos_of_zeros_in_boundary (lam i.rev)
        ((hcont i.rev).mono ((hRsub i false).trans (hISub i))) hz
        ⟨a i false, haR i false, hstrict i false⟩
    · exact (hRball i true).mapsTo_nonneg_of_zeros_in_boundary (lam i.rev)
        ((hcont i.rev).mono ((hRsub i true).trans (hISub i))) hz
        ⟨a i true, haR i true, hstrict i true⟩
  have hRopp (i : Fin 2) : rad i false ∩ rad i true = {m} := by
    apply Subset.antisymm
    · exact fun z hz => hRzero i false
        ⟨hz.1, le_antisymm (hRside i false z hz.1) (hRside i true z hz.2)⟩
    · rintro z rfl
      exact ⟨hmR i false, hmR i true⟩
  have hIunion (i : Fin 2) : I i = rad i false ∪ rad i true := by
    have hinter : segment ℝ (a i false) m ∩ segment ℝ m (a i true) = {m} := by
      simpa only [rad, segment_symm (𝕜 := ℝ) (a i false) m] using hRopp i
    have hb := isFinitePLBallPair_two_segments (hane i false) (hane i true).symm hinter
    have hb' : IsFinitePLBallPair ℝ (rad i false ∪ rad i true) {a i false, a i true} := by
      simpa only [rad, segment_symm (𝕜 := ℝ) (a i false) m] using hb
    exact (hb'.eq_of_subset_with_same_endpoints (hIball i)
      (union_subset (hRsub i false) (hRsub i true)) (hab i)).symm
  have hRcut (i : Fin 2) (sign : Bool) :
      rad i sign = I i ∩ {z | side sign (lam i.rev z)} := by
    apply Subset.antisymm
    · exact fun z hz => ⟨hRsub i sign hz, hRside i sign z hz⟩
    · rintro z ⟨hz, hzs⟩
      rcases (hIunion i).subset hz with hn | hp
      · cases sign
        · exact hn
        · have he : z = m := hRzero i false
            ⟨hn, le_antisymm (hRside i false z hn) hzs⟩
          exact he.symm ▸ hmR i true
      · cases sign
        · have he : z = m := hRzero i true
            ⟨hp, le_antisymm hzs (hRside i true z hp)⟩
          exact he.symm ▸ hmR i false
        · exact hp
  have hRrim (i : Fin 2) (sign : Bool) : rad i sign ∩ q = {a i sign} := by
    apply Subset.antisymm
    · rintro z ⟨hz, hzq⟩
      rcases (hIq i).subset ⟨hRsub i sign hz, hzq⟩ with hn | hp
      · cases sign
        · exact hn
        · have hs := hRside i true z hz
          rw [hn] at hs
          exact (not_le_of_gt (hstrict i false) hs).elim
      · cases sign
        · have hs := hRside i false z hz
          rw [hp] at hs
          exact (not_le_of_gt (hstrict i true) hs).elim
        · exact hp
    · rintro z rfl
      exact ⟨haR i sign, haq i sign⟩
  have hRcross (eps delta : Bool) : rad 0 delta ∩ rad 1 eps = {m} := by
    apply Subset.antisymm
    · exact fun z hz => hcrossI.subset ⟨hRsub 0 delta hz.1, hRsub 1 eps hz.2⟩
    · rintro z rfl
      exact ⟨hmR 0 delta, hmR 1 eps⟩
  let D := fun eps : Bool => J.space ∩ {z | side eps (lam 0 z)}
  let bD := fun eps : Bool => (q ∩ {z | side eps (lam 0 z)}) ∪ I 0
  have hD (eps : Bool) : IsFinitePLBallPair P2 (D eps) (bD eps) := by
    have hh := hJ.signed_halves_of_zero_arc (lam 0) (hcont 0) (hIball 0) (hab 0)
      (hzero 0) (hqzero 0) ⟨a 1 false, haq 1 false, hstrict 1 false⟩
      ⟨a 1 true, haq 1 true, hstrict 1 true⟩
    cases eps
    · exact hh.1
    · change IsFinitePLBallPair P2 (J.space ∩ {z | 0 ≤ lam 0 z})
        ((q ∩ {z | 0 ≤ lam 0 z}) ∪ I 0)
      rw [union_comm]
      exact hh.2
  have hDzero (eps : Bool) : D eps ∩ {z | lam 1 z = 0} = rad 1 eps := by
    rw [hRcut 1 eps]
    ext z
    exact ⟨fun h => ⟨(hzero 1).subset ⟨h.1.1, h.2⟩, h.1.2⟩,
      fun h => ⟨⟨((hzero 1).symm.subset h.1).1, h.2⟩, ((hzero 1).symm.subset h.1).2⟩⟩
  have hbDzero (eps : Bool) : bD eps ∩ {z | lam 1 z = 0} = {m, a 1 eps} := by
    apply Subset.antisymm
    · rintro z ⟨(hz | hz), hz1⟩
      · have hzR := (hRcut 1 eps).symm.subset
          ⟨(hzero 1).subset ⟨hJ.1 hz.1, hz1⟩, hz.2⟩
        exact Or.inr ((hRrim 1 eps).subset ⟨hzR, hz.1⟩)
      · exact Or.inl (hcrossI.subset ⟨hz, (hzero 1).subset ⟨hISub 0 hz, hz1⟩⟩)
    · rintro z (rfl | rfl)
      · exact ⟨Or.inr (hmI 0).1, hmzero 1⟩
      · exact ⟨Or.inl ⟨haq 1 eps, hRside 1 eps _ (haR 1 eps)⟩,
          ((hzero 1).symm.subset (hRsub 1 eps (haR 1 eps))).2⟩
  have hQball (eps delta : Bool) : IsFinitePLBallPair P2 (Q eps delta)
      ((Q eps delta ∩ q) ∪ (rad 0 delta ∪ rad 1 eps)) := by
    have hh := (hD eps).signed_halves_of_zero_arc (lam 1)
      ((hcont 1).mono inter_subset_left) (hRball 1 eps) (hane 1 eps).symm
      (hDzero eps) (hbDzero eps)
      ⟨a 0 false, Or.inr (hRsub 0 false (haR 0 false)), hstrict 0 false⟩
      ⟨a 0 true, Or.inr (hRsub 0 true (haR 0 true)), hstrict 0 true⟩
    have hb : IsFinitePLBallPair P2 (D eps ∩ {z | side delta (lam 1 z)})
        ((bD eps ∩ {z | side delta (lam 1 z)}) ∪ rad 1 eps) := by
      cases delta
      · exact hh.1
      · change IsFinitePLBallPair P2 (D eps ∩ {z | 0 ≤ lam 1 z})
          ((bD eps ∩ {z | 0 ≤ lam 1 z}) ∪ rad 1 eps)
        rw [union_comm]
        exact hh.2
    have hcarrier : D eps ∩ {z | side delta (lam 1 z)} = Q eps delta := by
      ext z
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    have houter : (q ∩ {z | side eps (lam 0 z)}) ∩ {z | side delta (lam 1 z)} =
        Q eps delta ∩ q := by
      ext z
      exact ⟨fun h => ⟨⟨hJ.1 h.1.1, h.1.2, h.2⟩, h.1.1⟩,
        fun h => ⟨⟨h.2, h.1.2.1⟩, h.1.2.2⟩⟩
    have hrim : (bD eps ∩ {z | side delta (lam 1 z)}) ∪ rad 1 eps =
        (Q eps delta ∩ q) ∪ (rad 0 delta ∪ rad 1 eps) := by
      have hrad : rad 0 delta = I 0 ∩ {z | side delta (lam 1 z)} := hRcut 0 delta
      change (((q ∩ {z | side eps (lam 0 z)}) ∪ I 0) ∩
        {z | side delta (lam 1 z)}) ∪ rad 1 eps = _
      rw [union_inter_distrib_right, houter, ← hrad, union_assoc]
    simpa only [hcarrier, hrim] using hb
  have hQsheet0 (eps delta : Bool) : Q eps delta ∩ (M (sheet 0)).space = rad 0 delta := by
    rw [hRcut 0 delta, hIs 0]
    ext z
    constructor
    · exact fun h => ⟨⟨h.1.1, h.2⟩, h.1.2.2⟩
    · intro h
      have hz0 : lam 0 z = 0 := ((hzero 0).symm.subset ((hIs 0).symm.subset h.1)).2
      refine ⟨⟨h.1.1, ?_, h.2⟩, h.1.2⟩
      cases eps <;> simp [side, hz0]
  have hQsheet1 (eps delta : Bool) : Q eps delta ∩ (M (sheet 1)).space = rad 1 eps := by
    rw [hRcut 1 eps, hIs 1]
    ext z
    constructor
    · exact fun h => ⟨⟨h.1.1, h.2⟩, h.1.2.1⟩
    · intro h
      have hz1 : lam 1 z = 0 := ((hzero 1).symm.subset ((hIs 1).symm.subset h.1)).2
      refine ⟨⟨h.1.1, h.2, ?_⟩, h.1.2⟩
      cases delta <;> simp [side, hz1]
  have hR0Q (eps delta : Bool) : rad 0 delta ⊆ Q eps delta :=
    fun _ hz => ((hQsheet0 eps delta).symm.subset hz).1
  have hR1Q (eps delta : Bool) : rad 1 eps ⊆ Q eps delta :=
    fun _ hz => ((hQsheet1 eps delta).symm.subset hz).1
  have hcompare (v : (M arc).vertices) (hvs : (v : E) ∈ s) :
      ∃ eta : Fin 2 → Bool,
        (∀ i : Fin 2,
          if eta i then
            B v (g (a i.rev false)) i.castSucc < 0 ∧
              0 < B v (g (a i.rev true)) i.castSucc
          else
            0 < B v (g (a i.rev false)) i.castSucc ∧
              B v (g (a i.rev true)) i.castSucc < 0) ∧
        ∀ (i : Fin 2) (sign : Bool) z, z ∈ J.space →
          (side sign (lam i z) ↔
            side (if eta i then sign else !sign) (B v (g z) i.castSucc)) := by
    let mu : Fin 2 → E → ℝ := fun i z => B v (g z) i.castSucc
    have hvK : (v : E) ∈ K.vertices := hMK arc v.property
    have hstarK : (K.closedStar v).space ⊆ K.space := space_subset_of_le (fun _ ht => ht.1)
    have hJstarv : J.space ⊆ (K.closedStar v).space := by
      intro z hz
      have hV := space_subset_of_le (K.barycentricDualBlock_antitone
        (Finset.singleton_subset_iff.mpr hvs)) hz
      obtain ⟨w, hw, hzw⟩ := mem_space_iff.mp hV
      obtain ⟨t, ht, hwt⟩ := K.exists_original_star_face_of_vertex_dual_face hvK hw
      exact (K.closedStar v).convexHull_subset_space ht (hwt hzw)
    have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
      rw [← hH (g z)]
      have he : g z = H.symm ⟨z, hz⟩ := Subtype.ext (hg ⟨z, hz⟩)
      rw [he, H.apply_symm_apply]
    have hvinj : InjOn (fun z => B v (g z)) (K.closedStar v).space := by
      intro x hx y hy he
      have hxy : (g x : X) = (g y : X) := (B v).injOn ((hB v).1 hx) ((hB v).1 hy) he
      exact (hFg x (hstarK hx)).symm.trans ((congrArg F hxy).trans (hFg y (hstarK hy)))
    have hvcont (i : Fin 2) : ContinuousOn (mu i) J.space :=
      (continuous_apply i.castSucc).comp_continuousOn
        ((B v).continuousOn.comp (hgPL.continuousOn.mono hJK)
          (fun _ hz => (hB v).1 (hJstarv hz)))
    have hvzero (i : Fin 2) : J.space ∩ {z | mu i z = 0} = I i := by
      rw [hIs]
      ext z
      constructor
      · rintro ⟨hz, hzi⟩
        exact ⟨hz, (hsheet i z (hJK hz)).mpr
          (((hB v).2.2.2 i (g z) ((hB v).1 (hJstarv hz))).mpr
            ⟨interior_subset (hJR hz), hzi⟩)⟩
      · rintro ⟨hz, hzi⟩
        exact ⟨hz, (((hB v).2.2.2 i (g z) ((hB v).1 (hJstarv hz))).mp
          ((hsheet i z (hJK hz)).mp hzi)).2⟩
    have hsigns (i : Fin 2) : ∃ eta : Bool,
        if eta then mu i (a i.rev false) < 0 ∧ 0 < mu i (a i.rev true)
          else 0 < mu i (a i.rev false) ∧ mu i (a i.rev true) < 0 := by
      let N := (M (sheet i.rev)).closedStar v
      let r : V3 →ᴬ[ℝ] P2 := ((ContinuousLinearMap.proj i.castSucc).prod
        (ContinuousLinearMap.proj (2 : Fin 3))).toContinuousAffineMap
      let ell : E → P2 := fun z => r (B v (g z))
      have hNK : N ≤ K.closedStar v := fun _ hw =>
        ⟨hMK (sheet i.rev) hw.1, hMK (sheet i.rev) hw.2⟩
      have hNz (z : E) (hz : z ∈ N.space) : B v (g z) i.rev.castSucc = 0 := by
        have hzstar := space_subset_of_le hNK hz
        have hzS := space_subset_of_le (show N ≤ M (sheet i.rev) from fun _ hw => hw.1) hz
        exact (((hB v).2.2.2 i.rev (g z) ((hB v).1 hzstar)).mp
          ((hsheet i.rev z (hstarK hzstar)).mp hzS)).2
      have hell : N.AffineOnFaces ell :=
        (show N.AffineOnFaces (fun z => B v (g z)) from
          fun w hw => (hB v).2.1 w (hNK hw)).postcomp r
      have helli : InjOn ell N.space := by
        intro x hx y hy he
        apply hvinj (space_subset_of_le hNK hx) (space_subset_of_le hNK hy)
        have hf0 := congrArg Prod.fst he
        have hf1 := congrArg Prod.snd he
        ext j
        fin_cases i <;> fin_cases j
        · exact hf0
        · exact (hNz x hx).trans (hNz y hy).symm
        · exact hf1
        · exact (hNz x hx).trans (hNz y hy).symm
        · exact hf0
        · exact hf1
      obtain ⟨htf, hst, htc⟩ := hcoface i.rev false
      obtain ⟨huf, hsu, huc⟩ := hcoface i.rev true
      have hsf : s ∈ (M (sheet i.rev)).faces :=
        (M (sheet i.rev)).down_closed htf hst ((M arc).nonempty_of_mem_faces hs)
      have hsN : s ∈ N.faces :=
        ⟨hsf, by simpa only [Finset.insert_eq_of_mem hvs] using hsf⟩
      have htN : T i.rev false ∈ N.faces :=
        ⟨htf, by simpa only [Finset.insert_eq_of_mem (hst hvs)] using htf⟩
      have huN : T i.rev true ∈ N.faces :=
        ⟨huf, by simpa only [Finset.insert_eq_of_mem (hsu hvs)] using huf⟩
      have htu : T i.rev false ≠ T i.rev true :=
        fun he => hab i.rev (congrArg (fun w : Finset E => w.centroid ℝ id) he)
      have hsign := hell.opposite_centroid_signs helli hsN htN huN
        (by simpa using hcard) (by simpa using htc) (by simpa using huc)
        hst hsu htu (LinearMap.fst ℝ ℝ ℝ).toAffineMap
        (by intro hz; have h := congrArg (fun L : P2 →ₗ[ℝ] ℝ => L (1, 0)) hz; norm_num at h)
        (by
          intro z hzs
          have hzstar : z ∈ (K.closedStar v).space :=
            (K.closedStar v).subset_space
              ⟨hMK arc hs, by simpa only [Finset.insert_eq_of_mem hvs] using hMK arc hs⟩ hzs
          have hzA := (harc z (hstarK hzstar)).mp ((M arc).subset_space hs hzs)
          have hz0 := (((hB v).2.2.1 (g z) ((hB v).1 hzstar)).mp hzA).2
          change B v (g z) i.castSucc = 0
          fin_cases i
          · exact hz0.1
          · exact hz0.2)
      change (mu i (a i.rev false) < 0 ∧ 0 < mu i (a i.rev true)) ∨
        (0 < mu i (a i.rev false) ∧ mu i (a i.rev true) < 0) at hsign
      exact hsign.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
    choose eta heta using hsigns
    have hhalfsign (i : Fin 2) (sign : Bool) :
        MapsTo (mu i) (J.space ∩ {z | side sign (lam i z)})
          {y | side (if eta i then sign else !sign) y} := by
      have hh := hJ.signed_halves_of_zero_arc (lam i) (hcont i) (hIball i) (hab i)
        (hzero i) (hqzero i)
        ⟨a i.rev false, haq i.rev false, by
          simpa only [Fin.rev_rev, Bool.false_eq_true, if_false] using hstrict i.rev false⟩
        ⟨a i.rev true, haq i.rev true, by
          simpa only [Fin.rev_rev, if_true] using hstrict i.rev true⟩
      have hd : IsFinitePLBallPair P2 (J.space ∩ {z | side sign (lam i z)})
          ((q ∩ {z | side sign (lam i z)}) ∪ I i) := by
        cases sign
        · exact hh.1
        · change IsFinitePLBallPair P2 (J.space ∩ {z | 0 ≤ lam i z})
            ((q ∩ {z | 0 ≤ lam i z}) ∪ I i)
          rw [union_comm]
          exact hh.2
      have hz : (J.space ∩ {z | side sign (lam i z)}) ∩ {z | mu i z = 0} ⊆
          (q ∩ {z | side sign (lam i z)}) ∪ I i :=
        fun z hz => Or.inr ((hvzero i).subset ⟨hz.1.1, hz.2⟩)
      have hw : a i.rev sign ∈ J.space ∩ {z | side sign (lam i z)} :=
        ⟨hISub i.rev (hRsub i.rev sign (haR i.rev sign)), by
          change side sign (lam i (a i.rev sign))
          simpa only [Fin.rev_rev] using hRside i.rev sign _ (haR i.rev sign)⟩
      have hi := heta i
      cases he : eta i <;> cases sign
      · change MapsTo (mu i) _ (Ici 0)
        exact hd.mapsTo_nonneg_of_zeros_in_boundary (mu i) ((hvcont i).mono inter_subset_left)
          hz ⟨a i.rev false, hw, (show 0 < mu i (a i.rev false) ∧
            mu i (a i.rev true) < 0 from by
              simpa only [he, Bool.false_eq_true, if_false] using hi).1⟩
      · change MapsTo (mu i) _ (Iic 0)
        exact hd.mapsTo_nonpos_of_zeros_in_boundary (mu i) ((hvcont i).mono inter_subset_left)
          hz ⟨a i.rev true, hw, (show 0 < mu i (a i.rev false) ∧
            mu i (a i.rev true) < 0 from by
              simpa only [he, Bool.false_eq_true, if_false] using hi).2⟩
      · change MapsTo (mu i) _ (Iic 0)
        exact hd.mapsTo_nonpos_of_zeros_in_boundary (mu i) ((hvcont i).mono inter_subset_left)
          hz ⟨a i.rev false, hw, (show mu i (a i.rev false) < 0 ∧
            0 < mu i (a i.rev true) from by simpa only [he, if_true] using hi).1⟩
      · change MapsTo (mu i) _ (Ici 0)
        exact hd.mapsTo_nonneg_of_zeros_in_boundary (mu i) ((hvcont i).mono inter_subset_left)
          hz ⟨a i.rev true, hw, (show mu i (a i.rev false) < 0 ∧
            0 < mu i (a i.rev true) from by simpa only [he, if_true] using hi).2⟩
    refine ⟨eta, heta, ?_⟩
    intro i sign z hz
    refine ⟨fun h => hhalfsign i sign ⟨hz, h⟩, ?_⟩
    intro h
    by_cases hside : side sign (lam i z)
    · exact hside
    have hother : side (!sign) (lam i z) := by
      cases sign
      · exact le_of_lt (lt_of_not_ge hside)
      · exact le_of_lt (lt_of_not_ge hside)
    have hw : side (if eta i then !sign else !(!sign)) (mu i z) :=
      hhalfsign i (!sign) ⟨hz, hother⟩
    have hnot : (if eta i then !sign else !(!sign)) = !(if eta i then sign else !sign) := by
      cases eta i <;> rfl
    rw [hnot] at hw
    have hboth (d : Bool) (x : ℝ) (ha : side d x) (hb : side (!d) x) : x = 0 := by
      cases d
      · exact le_antisymm ha hb
      · exact le_antisymm hb ha
    have hmu := hboth (if eta i then sign else !sign) (mu i z) h hw
    have hz0 : lam i z = 0 := ((hzero i).symm.subset ((hvzero i).subset ⟨hz, hmu⟩)).2
    cases sign <;> simp only [side, hz0, le_rfl, if_true, Bool.false_eq_true, if_false]
  refine ⟨p, T, hps, hpR, hJ, hJR, hJreg, hmiss, hJarc, hlinks, hcrossI,
    ?_, ?_, ?_, ?_, hcompare⟩
  · intro i
    refine ⟨hIs i, hIball i, hIunion i, ?_, ?_⟩
    · obtain ⟨_, _, _, _, _, _, _, hco, _⟩ := ht i
      exact hco
    · intro sign
      exact ⟨(hcoface i sign).1, (hcoface i sign).2.1, (hcoface i sign).2.2,
        hane i sign, hRball i sign, hRrim i sign, hRcut i sign, hstrict i sign⟩
  · intro eps delta
    let U := rad 0 delta ∪ rad 1 eps
    let O := Q eps delta ∩ q
    have hUQ : U ⊆ Q eps delta := union_subset (hR0Q eps delta) (hR1Q eps delta)
    have hUball : IsFinitePLBallPair ℝ U {a 0 delta, a 1 eps} := by
      have hinter : segment ℝ (a 0 delta) m ∩ segment ℝ m (a 1 eps) = {m} := by
        simpa only [rad, segment_symm (𝕜 := ℝ) (a 0 delta) m] using hRcross eps delta
      have hb := isFinitePLBallPair_two_segments (hane 0 delta) (hane 1 eps).symm hinter
      simpa only [rad, segment_symm (𝕜 := ℝ) (a 0 delta) m] using hb
    have hends : a 0 delta ≠ a 1 eps := by
      intro he
      exact hane 0 delta ((hRcross eps delta).subset
        ⟨haR 0 delta, he.symm ▸ haR 1 eps⟩)
    have hUO : U ∩ O = {a 0 delta, a 1 eps} := by
      apply Subset.antisymm
      · rintro z ⟨hz | hz, _, hzq⟩
        · exact Or.inl ((hRrim 0 delta).subset ⟨hz, hzq⟩)
        · exact Or.inr ((hRrim 1 eps).subset ⟨hz, hzq⟩)
      · rintro z (rfl | rfl)
        · exact ⟨Or.inl (haR 0 delta), hR0Q eps delta (haR 0 delta), haq 0 delta⟩
        · exact ⟨Or.inr (haR 1 eps), hR1Q eps delta (haR 1 eps), haq 1 eps⟩
    obtain ⟨O', hO', hwhole, hinter⟩ := (hQball eps delta).exists_boundary_arc_complement
      hUball subset_union_right hends
    have hOeq : O' = O := by
      apply Subset.antisymm
      · intro z hz
        by_cases hzU : z ∈ U
        · exact (hUO.symm.subset (hinter.subset ⟨hzU, hz⟩)).2
        · exact (hwhole.subset (Or.inr hz)).resolve_right hzU
      · intro z hz
        by_cases hzU : z ∈ U
        · exact hO'.1 (hUO.subset ⟨hzU, hz⟩)
        · exact (hwhole.symm.subset (Or.inl hz)).resolve_left hzU
    have hOball : IsFinitePLBallPair ℝ O {a 0 delta, a 1 eps} := by
      rw [← hOeq]
      exact hO'
    exact ⟨hQball eps delta, hUball, hOball, hUO,
      hQsheet0 eps delta, hQsheet1 eps delta, hRcross eps delta⟩
  · intro eps delta
    have hboth (sign : Bool) {x : ℝ} (hs : side sign x) (ht : side (!sign) x) : x = 0 := by
      cases sign
      · exact le_antisymm hs ht
      · exact le_antisymm ht hs
    have hmidQ (ep de : Bool) : m ∈ Q ep de := by
      refine ⟨hISub 0 (hmI 0).1, ?_, ?_⟩
      · cases ep <;> simp [side, hmzero]
      · cases de <;> simp [side, hmzero]
    refine ⟨?_, ?_, ?_⟩
    · apply Subset.antisymm
      · intro z hz
        have hz1 := hboth delta hz.1.2.2 hz.2.2.2
        apply (hQsheet1 eps delta).subset
        exact ⟨hz.1, ((hIs 1).subset ((hzero 1).subset ⟨hz.1.1, hz1⟩)).2⟩
      · exact fun z hz => ⟨hR1Q eps delta hz, hR1Q eps (!delta) hz⟩
    · apply Subset.antisymm
      · intro z hz
        have hz0 := hboth eps hz.1.2.1 hz.2.2.1
        apply (hQsheet0 eps delta).subset
        exact ⟨hz.1, ((hIs 0).subset ((hzero 0).subset ⟨hz.1.1, hz0⟩)).2⟩
      · exact fun z hz => ⟨hR0Q eps delta hz, hR0Q (!eps) delta hz⟩
    · apply Subset.antisymm
      · intro z hz
        exact hcrossI.subset ⟨(hzero 0).subset ⟨hz.1.1, hboth eps hz.1.2.1 hz.2.2.1⟩,
          (hzero 1).subset ⟨hz.1.1, hboth delta hz.1.2.2 hz.2.2.2⟩⟩
      · rintro z rfl
        exact ⟨hmidQ eps delta, hmidQ (!eps) (!delta)⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨eps, hz⟩ := mem_iUnion.mp hz
      obtain ⟨delta, hz⟩ := mem_iUnion.mp hz
      exact hz.1
    · intro hz
      have hsign (x : ℝ) : ∃ sign : Bool, side sign x := by
        rcases le_total x 0 with hx | hx
        · exact ⟨false, hx⟩
        · exact ⟨true, hx⟩
      obtain ⟨eps, heps⟩ := hsign (lam 0 z)
      obtain ⟨delta, hdelta⟩ := hsign (lam 1 z)
      exact mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hz, heps, hdelta⟩⟩

end PoincareConjecture.M76.Dehn
