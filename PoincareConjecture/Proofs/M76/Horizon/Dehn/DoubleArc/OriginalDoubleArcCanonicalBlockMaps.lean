import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcInteriorBlockMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcPrescribedEndpointBlock
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.PrescribedPrismInterval









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

section Original

variable {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

noncomputable local instance : DecidableEq E := Classical.decEq E

variable
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))

include hAC hAR hAF hF hH hg hgPL hMK hfull hreg hfr harc hsheet hB

open Classical in
theorem exists_original_canonical_interior_block_map_of_axis_superset
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
    {Aaxis : Set E} (bArc : I ≃ₜ Aaxis) (hbArc : bArc.IsFinitePL)
    (hZAaxis : (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space ⊆ Aaxis)
    (γ δ : I) (hγδ : γ < δ) (hsub : Icc (γ : ℝ) (δ : ℝ) ⊆ I)
    (axis : Icc (γ : ℝ) (δ : ℝ) ≃ₜ
      ↥((K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space))
    (haxis : ∀ t, (axis t : E) = bArc ⟨t, hsub t.property⟩)
    (htimes : ∀ j : Bool, (s j).centroid ℝ id = (bArc (if j then δ else γ) : E)) :
    ∃ map : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ)) ≃ₜ
      ((M reg).barycentricDualBlock {(v : E)}).space,
      map.IsFinitePL ∧
      (∀ j (x : signedTubeDiamond),
        (map ⟨(x, if j then (δ : ℝ) else (γ : ℝ)), x.property,
          by cases j <;> simp [show (γ : ℝ) ≤ δ from hγδ.le]⟩ : E) =
            G j (signedTubeDiamondReflection (eta j) x)) ∧
      (∀ t : Icc (γ : ℝ) (δ : ℝ),
        (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
      ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ))),
        (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
          (map x : E) ∈ ((M reg).barycentricDualBlock {(v : E)}).space ∩
            {z | ∀ i : Fin 2, if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
              else B v (g z) i.castSucc ≤ 0} := by
  classical
  obtain ⟨α, β, hlt, hsub', reverseEnds, halfMap, map, hmap, hhalf, hkeepHalf,
    hEnd, hAxis, hMem⟩ := exists_original_interior_block_map_of_joint_maps_of_axis_superset
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj G hG eta hQ hcenter bArc hbArc hZAaxis
  obtain ⟨_, hAxisEq⟩ := original_vertex_block_coordinate_marks S K (fun z => (g z : X))
    M hMK reg arc sheet hreg harc hsheet v (B v) (hB v).1 (hB v).2.2.1 (hB v).2.2.2
  have hZD : (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space ⊆
      ((M reg).barycentricDualBlock {(v : E)}).space :=
    fun _ hz => (hAxisEq.symm.subset hz).1
  have hExact := signed_prism_coordinate_axis_preimage map
    (fun i z => B v (g z) i.castSucc) hMem hAxisEq
  obtain ⟨hα, hβ⟩ := prescribed_prism_interval_eq bArc hZD hlt.le hγδ.le
    hsub' hsub map hExact hAxis axis haxis
  have hα' : α = γ := Subtype.ext hα
  have hβ' : β = δ := Subtype.ext hβ
  subst α
  subst β
  cases reverseEnds with
  | false => exact ⟨map, hmap, hEnd, hAxis, hMem⟩
  | true =>
      let zero : signedTubeDiamond := ⟨(0, 0),
        signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩
      have hzero : signedTubeDiamondReflection (eta true) zero = zero :=
        Subtype.ext (signedTubeReflection_zero _)
      have hend := hEnd false zero
      change (map ⟨(zero, (γ : ℝ)), zero.property, by simpa using
        (show (γ : ℝ) ∈ Icc (γ : ℝ) (δ : ℝ) from ⟨le_rfl, hγδ.le⟩)⟩ : E) =
          G true (signedTubeDiamondReflection (eta true) zero) at hend
      rw [hzero, hcenter, htimes] at hend
      have he : (bArc γ : E) = bArc δ := (hAxis ⟨γ, le_rfl, hγδ.le⟩).symm.trans hend
      exact (hγδ.ne (bArc.injective (Subtype.ext he))).elim

open Classical in
theorem exists_original_canonical_interior_block_map
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
    (bArc : I ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL)
    (γ δ : I) (hγδ : γ < δ) (hsub : Icc (γ : ℝ) (δ : ℝ) ⊆ I)
    (axis : Icc (γ : ℝ) (δ : ℝ) ≃ₜ
      ↥((K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space))
    (haxis : ∀ t, (axis t : E) = bArc ⟨t, hsub t.property⟩)
    (htimes : ∀ j : Bool, (s j).centroid ℝ id = (bArc (if j then δ else γ) : E)) :
    ∃ map : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ)) ≃ₜ
      ((M reg).barycentricDualBlock {(v : E)}).space,
      map.IsFinitePL ∧
      (∀ j (x : signedTubeDiamond),
        (map ⟨(x, if j then (δ : ℝ) else (γ : ℝ)), x.property,
          by cases j <;> simp [show (γ : ℝ) ≤ δ from hγδ.le]⟩ : E) =
            G j (signedTubeDiamondReflection (eta j) x)) ∧
      (∀ t : Icc (γ : ℝ) (δ : ℝ),
        (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
      ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ))),
        (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
          (map x : E) ∈ ((M reg).barycentricDualBlock {(v : E)}).space ∩
            {z | ∀ i : Fin 2, if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
              else B v (g z) i.castSucc ≤ 0} := by
  exact exists_original_canonical_interior_block_map_of_axis_superset
    hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
    hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj G hG eta hQ hcenter
    bArc hbArc inter_subset_right γ δ hγδ hsub axis haxis htimes

open Classical in


theorem exists_original_local_interior_block_map
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
        (s j).centroid ℝ id) :
    let Z := (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space
    let D := ((M reg).barycentricDualBlock {(v : E)}).space
    ∃ (b : I ≃ₜ Z) (map : ↥(signedTubeDiamond ×ˢ I) ≃ₜ D),
      b.IsFinitePL ∧
      (b ⟨0, le_rfl, zero_le_one⟩ : E) = (s false).centroid ℝ id ∧
      (b ⟨1, zero_le_one, le_rfl⟩ : E) = (s true).centroid ℝ id ∧
      map.IsFinitePL ∧
      (∀ j (x : signedTubeDiamond),
        (map ⟨(x, if j then (1 : ℝ) else 0), x.property,
          by cases j <;> simp⟩ : E) = G j (signedTubeDiamondReflection (eta j) x)) ∧
      (∀ t : I,
        (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : E) = b t) ∧
      (∀ eps delta (x : ↥(signedTubeDiamond ×ˢ I)),
        (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
          (map x : E) ∈ D ∩ {z | ∀ i : Fin 2,
            if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
              else B v (g z) i.castSucc ≤ 0}) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ I),
        (x : P2 × ℝ).1 = (0, 0) ↔ (map x : E) ∈ Z) ∧
      ∀ i (x : ↥(signedTubeDiamond ×ˢ I)),
        (x : P2 × ℝ).1 ∈ signedTubeSheet i ↔ (map x : E) ∈ (M (sheet i)).space := by
  classical
  obtain ⟨hZ, b, hb, hb0, hb1⟩ := exists_original_interior_axis_parameter
    hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet
    v (B v) (hB v).1 (hB v).2.1 (hB v).2.2.1 (hB v).2.2.2 hregion
    s hs hcard hvs hdisj
  obtain ⟨map, hmap, hends, haxis, hquarters⟩ :=
    exists_original_canonical_interior_block_map_of_axis_superset
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB v hvFr hregion s hs hcard hvs hdisj G hG eta hQ hcenter
      b hb Subset.rfl ⟨0, le_rfl, zero_le_one⟩ ⟨1, zero_le_one, le_rfl⟩
      zero_lt_one Subset.rfl b (fun _ => rfl) (by
        intro j
        cases j
        · exact hb0.symm
        · exact hb1.symm)
  obtain ⟨hSheet, hAxis⟩ := original_vertex_block_coordinate_marks S K
    (fun z => (g z : X)) M hMK reg arc sheet hreg harc hsheet v (B v)
    (hB v).1 (hB v).2.2.1 (hB v).2.2.2
  refine ⟨b, map, hb, hb0, hb1, hmap, hends, haxis, hquarters, ?_, ?_⟩
  · exact signed_prism_coordinate_axis_preimage map
      (fun i z => B v (g z) i.castSucc) hquarters hAxis
  · intro i x
    exact (signed_prism_coordinate_sheet_preimage map
      (fun i z => B v (g z) i.castSucc) hquarters i x).trans
        (hSheet i (map x) (map x).property).symm

open Classical in
theorem exists_original_canonical_endpoint_block_map
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2)
    (v : (M arc).vertices) (hvs : (v : E) ∈ s)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (hvFr : (g v : X) ∈ frontier R)
    (G : signedTubeDiamond ≃ₜ (K.barycentricDualBlock s).space)
    (hG : G.IsFinitePL) (eta : Fin 2 → Bool)
    (hQ : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector (K.barycentricDualBlock s).space
          (fun i z => B v (g z) i.castSucc) eta eps delta)
    (hcenter : (G ⟨(0, 0), signedTubeRadius_subset_diamond 0 false
      (left_mem_segment ℝ _ _)⟩ : E) = s.centroid ℝ id)
    (bArc : I ≃ₜ (M arc).space) (hbArc : bArc.IsFinitePL)
    (γ δ : I) (hγδ : γ < δ) (hsub : Icc (γ : ℝ) (δ : ℝ) ⊆ I)
    (axis : Icc (γ : ℝ) (δ : ℝ) ≃ₜ
      ↥((K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space))
    (haxis : ∀ t, (axis t : E) = bArc ⟨t, hsub t.property⟩)
    (jointEnd : Bool)
    (htime : s.centroid ℝ id = (bArc (if jointEnd then δ else γ) : E)) :
    ∃ (foot : signedTubeDiamond ≃ₜ
        ↥((K.barycentricDualBlock {(v : E)}).space ∩ (M fr).space))
      (map : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ)) ≃ₜ
        ((M reg).barycentricDualBlock {(v : E)}).space),
      foot.IsFinitePL ∧ map.IsFinitePL ∧
      (∀ j (x : signedTubeDiamond),
        (map ⟨(x, if j then (δ : ℝ) else (γ : ℝ)), x.property,
          by cases j <;> simp [show (γ : ℝ) ≤ δ from hγδ.le]⟩ : E) =
            if j = jointEnd then (G (signedTubeDiamondReflection eta x) : E) else foot x) ∧
      (∀ t : Icc (γ : ℝ) (δ : ℝ),
        (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : E) = bArc ⟨t, hsub t.property⟩) ∧
      ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc (γ : ℝ) (δ : ℝ))),
        (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
          (map x : E) ∈ ((M reg).barycentricDualBlock {(v : E)}).space ∩
            {z | ∀ i : Fin 2, if (![eps, delta] i) then 0 ≤ B v (g z) i.castSucc
              else B v (g z) i.castSucc ≤ 0} := by
  classical
  obtain ⟨foot, α, β, hlt, hsub', reverseEnds, map, hfoot, hmap, hEnd, hAxis, hMem⟩ :=
    exists_original_endpoint_block_map_of_joint_map hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard v hvs hregion hvFr
      G hG eta hQ hcenter bArc hbArc
  obtain ⟨_, hAxisEq⟩ := original_vertex_block_coordinate_marks S K (fun z => (g z : X))
    M hMK reg arc sheet hreg harc hsheet v (B v) (hB v).1 (hB v).2.2.1 (hB v).2.2.2
  have hZD : (K.barycentricDualBlock {(v : E)}).space ∩ (M arc).space ⊆
      ((M reg).barycentricDualBlock {(v : E)}).space :=
    fun _ hz => (hAxisEq.symm.subset hz).1
  have hExact := signed_prism_coordinate_axis_preimage map
    (fun i z => B v (g z) i.castSucc) hMem hAxisEq
  obtain ⟨hα, hβ⟩ := prescribed_prism_interval_eq bArc hZD hlt.le hγδ.le
    hsub' hsub map hExact hAxis axis haxis
  have hα' : α = γ := Subtype.ext hα
  have hβ' : β = δ := Subtype.ext hβ
  subst α
  subst β
  let aligned := (signedTubeDiamondReflection eta).trans G
  have hAlignedCenter : (aligned ⟨(0, 0), signedTubeRadius_subset_diamond 0 false
      (left_mem_segment ℝ _ _)⟩ : E) = bArc (if jointEnd then δ else γ) := by
    change (G (signedTubeDiamondReflection eta _) : E) = _
    have hz : signedTubeDiamondReflection eta ⟨(0, 0),
        signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
      ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ :=
        Subtype.ext (signedTubeReflection_zero eta)
    rw [hz, hcenter]
    exact htime
  have hJointEnd : ∀ x : signedTubeDiamond,
      (map ⟨(x, if !reverseEnds then (δ : ℝ) else (γ : ℝ)), x.property,
        by cases reverseEnds <;> simp [show (γ : ℝ) ≤ δ from hγδ.le]⟩ : E) = aligned x := by
    intro x
    have hh := hEnd (!reverseEnds) x
    cases reverseEnds <;> exact hh
  have hEndTime := prescribed_prism_end_time bArc hγδ.le hsub map aligned (!reverseEnds)
    (if jointEnd then δ else γ) hJointEnd hAlignedCenter hAxis
  have hJoint : (!reverseEnds) = jointEnd := by
    cases reverseEnds with
    | false =>
        cases jointEnd with
        | false => exact (hγδ.ne (Subtype.ext hEndTime.symm)).elim
        | true => rfl
    | true =>
        cases jointEnd with
        | false => rfl
        | true => exact (hγδ.ne (Subtype.ext hEndTime)).elim
  subst jointEnd
  refine ⟨foot, map, hfoot, hmap, ?_, hAxis, hMem⟩
  intro j x
  have hh := hEnd j x
  cases reverseEnds <;> cases j <;> exact hh

end Original

end PoincareConjecture.M76.Dehn
