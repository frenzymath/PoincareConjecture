import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcCanonicalBlockMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcAxisContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismChainMap

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in
theorem exists_original_signed_tube_map
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
    (hregion : ∀ v, (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (bArc : I ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL)
    (hcontact : (M arc).space ∩ (M fr).space =
      {(bArc ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E),
        (bArc ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E)}) :
    ∃ tube : ↥(signedTubeDiamond ×ˢ I) ≃ₜ ((M reg).barycentricNeighborhood (M arc)).space,
      tube.IsFinitePL ∧
      (∀ t : I, (tube ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc t) ∧
      (∀ i (x : ↥(signedTubeDiamond ×ˢ I)),
        (x : P2 × ℝ).1 ∈ signedTubeSheet i ↔ (tube x : E) ∈ (M (sheet i)).space) ∧
      ∀ x : ↥(signedTubeDiamond ×ˢ I),
        (tube x : E) ∈ (M fr).space ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1 := by
  classical
  obtain ⟨n, p, t, hsub, hp, ht, ht0, ht1, hverts, hedge, hcover, hmid, hAxes⟩ :=
    exists_original_signed_tube_axis_maps K (M arc) (M fr) (hMK arc) (hMK fr)
      (hfull arc) (hfull fr) bArc hbArc hcontact
  choose axis hAxisPL hAxis using hAxes
  obtain ⟨hp0, hp1, hlabels⟩ := original_axis_endpoint_labels K (M arc) (M fr)
    (hMK arc) (hMK fr) bArc hcontact p t hp ht ht0 ht1 hverts hsub axis hAxis
  have hvertex (i : Fin (n + 2)) : p i ∈ (M arc).vertices :=
    hverts.symm.subset (mem_range_self i)
  let v : Fin (n + 2) → (M arc).vertices := fun i => ⟨p i, hvertex i⟩
  have hfinite : ((M arc).space ∩ (M fr).space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hFr (i : Fin (n + 2)) : (g (p i) : X) ∈ frontier R ↔
      i = 0 ∨ i = Fin.last (n + 1) := by
    have hiK := K.vertices_subset_space (hMK arc (hvertex i))
    constructor
    · intro hi
      exact (hlabels i).mp ((mem_vertices_of_finite_subcomplex_intersection
        (hMK arc) (hMK fr) hfinite ((M arc).vertices_subset_space (hvertex i))
          ((hfr _ hiK).mpr hi)).2)
    · intro hi
      exact (hfr _ hiK).mp ((M fr).vertices_subset_space ((hlabels i).mpr hi))
  have hcard (j : Fin (n + 1)) : ({p j.castSucc, p j.succ} : Finset E).card = 2 := by
    apply Finset.card_pair
    intro he
    have hh := congrArg Fin.val (hp he)
    change j.val = j.val + 1 at hh
    omega
  let Edge := {s : Finset E // s ∈ (M arc).faces ∧ s.card = 2}
  let edge : Fin (n + 1) → Edge := fun j => ⟨{p j.castSucc, p j.succ}, hedge j, hcard j⟩
  obtain ⟨G, eta, hG, hcenter, hQ⟩ := exists_original_signed_tube_joint_family
    hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB
  let D := fun i : Fin (n + 2) => ((M reg).barycentricDualBlock {p i}).space
  let J := fun j : Fin (n + 1) => (K.barycentricDualBlock (edge j)).space
  let joint : ∀ j : Fin (n + 1), signedTubeDiamond ≃ₜ J j := fun j => G (edge j)
  let left := fun j : Fin (n + 1) => eta (edge j) (v j.castSucc) (Finset.mem_insert_self _ _)
  let right := fun j : Fin (n + 1) => eta (edge j) (v j.succ)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨hcontacts, hlinks, hfar, hjoints⟩ := K.full_arc_dual_contacts
    (M arc) (hMK arc) (hfull arc) p hp hvertex hedge hcover
  have hDV (i : Fin (n + 2)) : D i ⊆ (K.barycentricDualBlock {p i}).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {p i}).symm.subset.trans
      inter_subset_left
  have hMaps (i : Fin (n + 2)) :
      ∃ map : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) ≃ₜ D i,
        map.IsFinitePL ∧
        (∀ (j : Fin (n + 1)), j.castSucc = i → ∀ x : signedTubeDiamond,
          (map ⟨(x, (t i.succ : ℝ)), x.property, (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) =
            joint j (signedTubeDiamondReflection (left j) x)) ∧
        (∀ (j : Fin (n + 1)), j.succ = i → ∀ x : signedTubeDiamond,
          (map ⟨(x, (t i.castSucc : ℝ)), x.property, le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) =
            joint j (signedTubeDiamondReflection (right j) x)) ∧
        (∀ u : Icc (t i.castSucc : ℝ) (t i.succ : ℝ),
          (map ⟨((0, 0), u), signedTubeRadius_subset_diamond 0 false
            (left_mem_segment ℝ _ _), u.property⟩ : E) = bArc ⟨u, hsub i u.property⟩) ∧
        (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔ (map x : E) ∈ (M (sheet k)).space) ∧
        ∀ x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)),
          (map x : E) ∈ (M fr).space ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1 := by
    have hmarks := (original_vertex_block_coordinate_marks S K (fun z => (g z : X))
      M hMK reg arc sheet hreg harc hsheet (v i) (B (v i))
      (hB (v i)).1 (hB (v i)).2.2.1 (hB (v i)).2.2.2).1
    have hSheet (map : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) ≃ₜ D i)
        (hmem : ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
            (map x : E) ∈ D i ∩ {z | ∀ k : Fin 2,
              if (![eps, delta] k) then 0 ≤ B (v i) (g z) k.castSucc
                else B (v i) (g z) k.castSucc ≤ 0}) :
        ∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ))),
          (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔ (map x : E) ∈ (M (sheet k)).space := by
      intro k x
      exact (signed_prism_coordinate_sheet_preimage map
        (fun k z => B (v i) (g z) k.castSucc) hmem k x).trans
          (hmarks k (map x) (map x).property).symm
    have hFoot (map : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) ≃ₜ D i)
        (foot : signedTubeDiamond ≃ₜ ↥((K.barycentricDualBlock {p i}).space ∩ (M fr).space))
        (u : Icc (t i.castSucc : ℝ) (t i.succ : ℝ))
        (hkeep : ∀ x : signedTubeDiamond, (map ⟨(x, u), x.property, u.property⟩ : E) = foot x)
        (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ))) :
        (map x : E) ∈ (M fr).space ↔ (x : P2 × ℝ).2 = u := by
      have hmem : (map x : E) ∈ (M fr).space ↔
          (map x : E) ∈ (K.barycentricDualBlock {p i}).space ∩ (M fr).space :=
        ⟨fun hx => ⟨hDV i (map x).property, hx⟩, fun hx => hx.2⟩
      exact hmem.trans (signed_prism_end_preimage u.property map foot hkeep x)
    by_cases hi0 : i = 0
    · subst i
      obtain ⟨foot, map, hfoot, hmap, hEnd, hAx, hMem⟩ :=
        exists_original_canonical_endpoint_block_map hAC hAR hAF S K F hF H hH g hg hgPL
          M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB
          (edge 0) (hedge 0) (hcard 0) (v 0) (Finset.mem_insert_self _ _)
          (hregion (v 0)) ((hFr 0).mpr (Or.inl rfl)) (joint 0) (hG (edge 0)) (left 0)
          (hQ (edge 0) (v 0) (Finset.mem_insert_self _ _)) (hcenter (edge 0)) bArc hbArc
          (t (0 : Fin (n + 2)).castSucc) (t (0 : Fin (n + 2)).succ)
          (ht Fin.castSucc_lt_succ) (hsub 0) (axis 0) (hAxis 0) true (hmid 0).symm
      refine ⟨map, hmap, ?_, ?_, hAx, hSheet map hMem, ?_⟩
      · intro j hj x
        have hj0 : j = 0 := Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) hj)
        subst j
        exact hEnd true x
      · intro j hj x
        have hh := congrArg Fin.val hj
        change j.val + 1 = 0 at hh
        omega
      · intro x
        have hh := hFoot map foot ⟨t (0 : Fin (n + 2)).castSucc, le_rfl,
          (ht Fin.castSucc_lt_succ).le⟩ (hEnd false) x
        have hmax : (t (0 : Fin (n + 2)).succ : ℝ) < 1 := by
          have hh : (t (0 : Fin (n + 2)).succ : ℝ) < t (Fin.last (n + 2)) :=
            ht (show (0 : Fin (n + 2)).succ < Fin.last (n + 2) from by
            change 1 < n + 2
            omega)
          simpa only [ht1] using hh
        have hne : (x : P2 × ℝ).2 ≠ 1 := (x.property.2.2.trans_lt hmax).ne
        change (map x : E) ∈ (M fr).space ↔ (x : P2 × ℝ).2 = (t 0 : ℝ) at hh
        rw [ht0] at hh
        exact hh.trans ⟨Or.inl, fun hx => hx.resolve_right hne⟩
    by_cases hiLast : i = Fin.last (n + 1)
    · subst i
      let j : Fin (n + 1) := Fin.last n
      have hj : j.succ = Fin.last (n + 1) := Fin.ext rfl
      have hjtime : j.castSucc.succ = (Fin.last (n + 1)).castSucc := Fin.ext rfl
      obtain ⟨foot, map, hfoot, hmap, hEnd, hAx, hMem⟩ :=
        exists_original_canonical_endpoint_block_map hAC hAR hAF S K F hF H hH g hg hgPL
          M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB
          (edge j) (hedge j) (hcard j) (v (Fin.last (n + 1)))
          (by change p (Fin.last (n + 1)) ∈ ({p j.castSucc, p j.succ} : Finset E); rw [← hj]; simp)
          (hregion (v _)) ((hFr _).mpr (Or.inr rfl)) (joint j) (hG (edge j)) (right j)
          (by simpa only [hj] using (hQ (edge j) (v j.succ)
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
          (hcenter (edge j)) bArc hbArc
          (t (Fin.last (n + 1)).castSucc) (t (Fin.last (n + 1)).succ)
          (ht Fin.castSucc_lt_succ) (hsub _) (axis _) (hAxis _) false
          (by simpa only [edge, Bool.false_eq_true, ↓reduceIte, hjtime] using (hmid j).symm)
      refine ⟨map, hmap, ?_, ?_, hAx, hSheet map hMem, ?_⟩
      · intro k hk x
        have hh := congrArg Fin.val hk
        change k.val = n + 1 at hh
        have hklt := k.isLt
        omega
      · intro k hk x
        have hkj : k = j := by
          apply Fin.ext
          have hh := congrArg Fin.val hk
          change k.val + 1 = n + 1 at hh
          change k.val = n
          omega
        subst k
        exact hEnd false x
      · intro x
        have hh := hFoot map foot ⟨t (Fin.last (n + 1)).succ,
          (ht Fin.castSucc_lt_succ).le, le_rfl⟩ (hEnd true) x
        have hmin : 0 < (t (Fin.last (n + 1)).castSucc : ℝ) := by
          have hh : (t 0 : ℝ) < t (Fin.last (n + 1)).castSucc :=
            ht (show (0 : Fin (n + 3)) < (Fin.last (n + 1)).castSucc from by
            change 0 < n + 1
            omega)
          simpa only [ht0] using hh
        have hne : (x : P2 × ℝ).2 ≠ 0 := (hmin.trans_le x.property.2.1).ne'
        change (map x : E) ∈ (M fr).space ↔
          (x : P2 × ℝ).2 = (t (Fin.last (n + 2)) : ℝ) at hh
        rw [ht1] at hh
        exact hh.trans ⟨Or.inr, fun hx => hx.resolve_left hne⟩
    · have hiPos : 0 < i.val := by
        by_contra hn
        apply hi0
        apply Fin.ext
        change i.val = 0
        omega
      have hiBound : i.val < n + 1 := by
        by_contra hn
        apply hiLast
        apply Fin.ext
        change i.val = n + 1
        have hh := i.isLt
        omega
      let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let k : Fin (n + 1) := ⟨i.val, hiBound⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have hk : k.castSucc = i := Fin.ext rfl
      have hjtime : j.castSucc.succ = i.castSucc := Fin.ext (by simp [j]; omega)
      have hktime : k.castSucc.succ = i.succ := Fin.ext rfl
      let ends : Bool → Fin (n + 1) := fun side => if side then k else j
      let signs : Bool → Fin 2 → Bool := fun side => if side then left k else right j
      have hvs (side : Bool) : (v i : E) ∈ (edge (ends side) : Finset E) := by
        cases side
        · change p i ∈ ({p j.castSucc, p j.succ} : Finset E)
          rw [← hj]
          simp
        · change p i ∈ ({p k.castSucc, p k.succ} : Finset E)
          rw [← hk]
          simp
      have hQs (side : Bool) : ∀ eps delta (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeQuarter eps delta ↔
            (joint (ends side) x : E) ∈ signedCoordinateSector (J (ends side))
              (fun l z => B (v i) (g z) l.castSucc) (signs side) eps delta := by
        cases side
        · change ∀ eps delta (x : signedTubeDiamond), (x : P2) ∈ signedTubeQuarter eps delta ↔
            (joint j x : E) ∈ signedCoordinateSector (J j)
              (fun l z => B (v i) (g z) l.castSucc) (right j) eps delta
          simpa only [hj] using (hQ (edge j) (v j.succ)
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        · change ∀ eps delta (x : signedTubeDiamond), (x : P2) ∈ signedTubeQuarter eps delta ↔
            (joint k x : E) ∈ signedCoordinateSector (J k)
              (fun l z => B (v i) (g z) l.castSucc) (left k) eps delta
          simpa only [hk] using
            (hQ (edge k) (v k.castSucc) (Finset.mem_insert_self _ _))
      have hdisj : Disjoint (J j) (J k) := hjoints j k (by
        intro he
        have hh := congrArg Fin.val he
        change i.val - 1 = i.val at hh
        omega)
      obtain ⟨map, hmap, hEnd, hAx, hMem⟩ :=
        exists_original_canonical_interior_block_map hAC hAR hAF S K F hF H hH g hg hgPL
          M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB
          (v i) (fun hx => (hFr i).mp hx |>.elim hi0 hiLast) (hregion (v i))
          (fun side => edge (ends side)) (fun side => hedge (ends side))
          (fun side => hcard (ends side)) hvs hdisj
          (fun side => joint (ends side)) (fun side => hG (edge (ends side))) signs hQs
          (fun side => hcenter (edge (ends side))) bArc hbArc
          (t i.castSucc) (t i.succ) (ht Fin.castSucc_lt_succ) (hsub i) (axis i) (hAxis i)
          (by intro side; cases side
              · simpa only [ends, edge, Bool.false_eq_true, ↓reduceIte, hjtime] using (hmid j).symm
              · simpa only [ends, edge, ↓reduceIte, hktime] using (hmid k).symm)
      refine ⟨map, hmap, ?_, ?_, hAx, hSheet map hMem, ?_⟩
      · intro l hl x
        have hlk : l = k := Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) hl)
        subst l
        exact hEnd true x
      · intro l hl x
        have hlj : l = j := by
          apply Fin.ext
          have hh := congrArg Fin.val hl
          change l.val + 1 = i.val at hh
          change l.val = i.val - 1
          omega
        subst l
        exact hEnd false x
      · intro x
        have hnot : p i ∉ (M fr).vertices := fun hx => ((hlabels i).mp hx).elim hi0 hiLast
        have havoid : (K.barycentricDualBlock {p i}).space ∩ (M fr).space = ∅ := by
          rw [K.barycentricDualBlock_space_inter_subcomplex (M fr) (hMK fr) {p i}]
          exact (M fr).barycentricDualBlock_space_eq_empty_of_not_face
            (Finset.singleton_nonempty _) hnot
        have hmin : 0 < (t i.castSucc : ℝ) := by
          have hh : (t 0 : ℝ) < t i.castSucc := ht (show (0 : Fin (n + 3)) < i.castSucc from hiPos)
          simpa only [ht0] using hh
        have hmax : (t i.succ : ℝ) < 1 := by
          have hh : (t i.succ : ℝ) < t (Fin.last (n + 2)) := ht (show i.succ < Fin.last (n + 2) from by
            change i.val + 1 < n + 2
            omega)
          simpa only [ht1] using hh
        exact iff_of_false
          (fun hx => (havoid.subset ⟨hDV i (map x).property, hx⟩).elim)
          (fun hx => hx.elim (hmin.trans_le x.property.2.1).ne'
            (x.property.2.2.trans_lt hmax).ne)
  choose maps hMapsPL hUpper hLower hMapAxis hMapSheet hMapFrontier using hMaps
  have hJointContact (j : Fin (n + 1)) : D j.castSucc ∩ D j.succ = J j := by
    apply Subset.antisymm
    · intro z hz
      exact (hcontacts j).subset ⟨hDV j.castSucc hz.1, hDV j.succ hz.2⟩
    · intro z hz
      constructor
      · obtain ⟨x, hx⟩ := ((signedTubeDiamondReflection (left j)).trans (joint j)).surjective ⟨z, hz⟩
        have hval := (hUpper j.castSucc j rfl x).trans (congrArg Subtype.val hx)
        have hzD := (maps j.castSucc ⟨(x, (t j.castSucc.succ : ℝ)), x.property,
          (ht Fin.castSucc_lt_succ).le, le_rfl⟩).property
        rwa [hval] at hzD
      · obtain ⟨x, hx⟩ := ((signedTubeDiamondReflection (right j)).trans (joint j)).surjective ⟨z, hz⟩
        have hval := (hLower j.succ j rfl x).trans (congrArg Subtype.val hx)
        have hzD := (maps j.succ ⟨(x, (t j.succ.castSucc : ℝ)), x.property,
          le_rfl, (ht Fin.castSucc_lt_succ).le⟩).property
        rwa [hval] at hzD
  have hDfar (i j : Fin (n + 2)) (hij : i.val + 1 < j.val) : Disjoint (D i) (D j) :=
    (hfar i j hij).mono (hDV i) (hDV j)
  have htr : StrictMono (fun i => (t i : ℝ)) := fun _ _ hij => ht hij
  obtain ⟨frame, tube, hframe0, htube, hKeep⟩ := exists_signed_prism_chain_map_of_incident_frames
    (fun i => (t i : ℝ)) htr D J joint (fun j => hG (edge j)) left right (fun _ => true)
    maps hMapsPL hJointContact hDfar (fun j => hUpper j.castSucc j rfl)
      (fun j => hLower j.succ j rfl)
  have hSource : signedTubeDiamond ×ˢ Icc (t 0 : ℝ) (t (Fin.last (n + 2)) : ℝ) =
      signedTubeDiamond ×ˢ I := by rw [ht0, ht1]
  have hTarget : (⋃ i, D i) = ((M reg).barycentricNeighborhood (M arc)).space := by
    rw [(M reg).barycentricNeighborhood_space_eq_iUnion_dualBlocks, hverts]
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion₂.mpr ⟨p i, mem_range_self i, hi⟩
    · intro hz
      obtain ⟨q, ⟨i, rfl⟩, hi⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion.mpr ⟨i, hi⟩
  let result := (Homeomorph.setCongr hSource.symm).trans (tube.trans (Homeomorph.setCongr hTarget))
  have hResult : result.IsFinitePL := htube.setCongr hSource hTarget
  have hKeepResult (i : Fin (n + 2))
      (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ))) :
      (result ⟨x, x.property.1, hsub i x.property.2⟩ : E) =
        maps i (signedTubePrismReparametrization (signedTubeDiamondReflection (frame i))
          (t i.castSucc) (t i.succ) x) := hKeep i x
  have hPiece (u : I) : ∃ i : Fin (n + 2), (u : ℝ) ∈ Icc (t i.castSucc : ℝ) (t i.succ : ℝ) := by
    apply htr.monotone.exists_mem_consecutive_Icc
    simpa only [ht0, ht1] using u.property
  refine ⟨result, hResult, ?_, ?_, ?_⟩
  · intro u
    obtain ⟨i, hi⟩ := hPiece u
    let x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) :=
      ⟨((0, 0), u), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _), hi⟩
    have hz : signedTubeDiamondReflection (frame i) ⟨(0, 0),
        signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
      ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ :=
        Subtype.ext (signedTubeReflection_zero _)
    have hReparam := signedTubePrismReparametrization_center
      (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ) hz ⟨u, hi⟩
    exact (hKeepResult i x).trans ((congrArg (fun z => (maps i z : E)) hReparam).trans
      (hMapAxis i ⟨u, hi⟩))
  · intro k x
    obtain ⟨i, hi⟩ := hPiece ⟨(x : P2 × ℝ).2, x.property.2⟩
    let y : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) :=
      ⟨x, x.property.1, hi⟩
    let r := signedTubePrismReparametrization (signedTubeDiamondReflection (frame i))
      (t i.castSucc) (t i.succ) y
    have hmem : (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔ (r : P2 × ℝ).1 ∈ signedTubeSheet k :=
      (signedTubeReflection_mem_sheet (frame i) k (x : P2 × ℝ).1).symm
    exact hmem.trans ((hMapSheet i k r).trans (by rw [← hKeepResult i y]))
  · intro x
    obtain ⟨i, hi⟩ := hPiece ⟨(x : P2 × ℝ).2, x.property.2⟩
    let y : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc : ℝ) (t i.succ : ℝ)) :=
      ⟨x, x.property.1, hi⟩
    rw [hKeepResult i y]
    exact hMapFrontier i (signedTubePrismReparametrization
      (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ) y)

end PoincareConjecture.M76.Dehn
