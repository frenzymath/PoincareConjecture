import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Logic.Equiv.PartialEquiv









set_option autoImplicit false

open Set Metric Topology
open scoped BigOperators

universe u

namespace Poincare.Topology



theorem exists_simplexCharacteristicMap {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Finset E) (hne : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ e : PartialEquiv (Fin (s.card - 1) → ℝ) E,
      e.source = ball 0 1 ∧
      e.target = intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      Continuous e ∧ ContinuousOn e.symm e.target ∧
      e '' closedBall 0 1 = convexHull ℝ (s : Set E) ∧
      e '' sphere 0 1 = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  let A := affineSpan ℝ (s : Set E)
  obtain ⟨p, hp⟩ := hne
  let origin : A := ⟨p, subset_affineSpan ℝ (s : Set E) hp⟩
  let : Nonempty A := ⟨origin⟩
  have hdim : Module.finrank ℝ A.direction = s.card - 1 := by
    have hc : Fintype.card s = (s.card - 1) + 1 := by
      rw [Fintype.card_coe, Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨p, hp⟩)]
    have hr : range (Subtype.val : s → E) = (s : Set E) := by ext x; simp
    have h := hi.finrank_vectorSpan hc
    rw [hr] at h
    change Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction = _
    rw [direction_affineSpan]
    exact h
  let coordinates : (Fin (s.card - 1) → ℝ) ≃ₗ[ℝ] A.direction :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hdim])
  let chart := coordinates.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ origin)
  let chartHomeo := chart.toContinuousAffineEquiv.toHomeomorph
  let embedding : (Fin (s.card - 1) → ℝ) →ᵃ[ℝ] E := A.subtype.comp chart.toAffineMap
  let body := embedding ⁻¹' convexHull ℝ (s : Set E)
  have he : IsEmbedding embedding := IsEmbedding.subtypeVal.comp chartHomeo.isEmbedding
  have hcover : convexHull ℝ (s : Set E) ⊆ range embedding := by
    intro x hx
    let y : A := ⟨x, convexHull_subset_affineSpan (s : Set E) hx⟩
    refine ⟨chart.symm y, ?_⟩
    change (chart (chart.symm y) : E) = x
    rw [chart.apply_symm_apply]
  have hc : IsCompact body :=
    he.isInducing.isCompact_preimage' (s.finite_toSet.isCompact_convexHull ℝ) hcover
  have hiBody : embedding '' interior body =
      intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rw [intrinsicInterior, affineSpan_convexHull]
    exact image_interior_preimage_comp chartHomeo chartHomeo.isHomeomorph
      (Subtype.val : A → E) (convexHull ℝ (s : Set E))
  have hfBody : embedding '' frontier body =
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [intrinsicFrontier, affineSpan_convexHull]
    exact image_frontier_preimage_comp chartHomeo chartHomeo.isHomeomorph
      (Subtype.val : A → E) (convexHull ℝ (s : Set E))
  have hclBody : embedding '' closure body = convexHull ℝ (s : Set E) := by
    rw [hc.isClosed.closure_eq]
    exact image_preimage_eq_of_subset hcover
  have hneBody : (interior body).Nonempty := by
    rw [← image_nonempty (f := embedding), hiBody]
    exact Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _)
      ⟨p, subset_convexHull ℝ (s : Set E) hp⟩
  obtain ⟨rescale, hball, hclosed, hsphere⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      ((convex_convexHull ℝ (s : Set E)).affine_preimage embedding) hneBody hc.isBounded
  have hball' : rescale.symm '' ball 0 1 = interior body := by
    rw [← hball]
    exact rescale.toEquiv.symm_image_image _
  have hclosed' : rescale.symm '' closedBall 0 1 = closure body := by
    rw [← hclosed]
    exact rescale.toEquiv.symm_image_image _
  have hsphere' : rescale.symm '' sphere 0 1 = frontier body := by
    rw [← hsphere]
    exact rescale.toEquiv.symm_image_image _
  let f := embedding ∘ rescale.symm
  have hf : IsEmbedding f := he.comp rescale.symm.isEmbedding
  let e := hf.injective.injOn.toPartialEquiv f (ball 0 1)
  refine ⟨e, rfl, ?_, hf.continuous, ?_, ?_, ?_⟩
  · change (embedding ∘ rescale.symm) '' ball 0 1 = _
    rw [image_comp, hball', hiBody]
  · change ContinuousOn e.symm (f '' ball 0 1)
    apply hf.isInducing.continuousOn_image_iff.mpr
    exact continuousOn_id.congr (fun x hx => e.left_inv hx)
  · change (embedding ∘ rescale.symm) '' closedBall 0 1 = _
    rw [image_comp, hclosed', hclBody]
  · change (embedding ∘ rescale.symm) '' sphere 0 1 = _
    rw [image_comp, hsphere', hfBody]

open scoped Classical in


theorem simplex_intrinsicFrontier {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset E) (hne : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → E)) :
    intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
      ⋃ i : s, convexHull ℝ (s.erase (i : E) : Set E) := by
  classical
  let A := affineSpan ℝ (s : Set E)
  obtain ⟨p, hp⟩ := hne
  let pA : A := ⟨p, subset_affineSpan ℝ (s : Set E) hp⟩
  let : Nonempty A := ⟨pA⟩
  let : Nonempty (s : Set E) := ⟨⟨p, hp⟩⟩
  let translate : A ≃ᵃⁱ[ℝ] A.direction := AffineIsometryEquiv.constVSub ℝ pA
  let vertices : s → A := fun i => ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩
  have hind : AffineIndependent ℝ vertices := by
    apply AffineIndependent.of_comp A.subtype
    exact hi
  have hspan : affineSpan ℝ (range vertices) = ⊤ := by
    have hr : range vertices = (Subtype.val : A → E) ⁻¹' (s : Set E) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro hx
        exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    rw [hr]
    exact affineSpan_coe_preimage_eq_top (s : Set E)
  let b : AffineBasis s ℝ A.direction := {
    toFun := translate ∘ vertices
    ind' := hind.map' translate.toAffineEquiv.toAffineMap translate.injective
    tot' := by
      rw [range_comp]
      exact translate.toAffineEquiv.toAffineMap.span_eq_top_of_surjective
        translate.surjective hspan }
  let inclusion : A.direction →ᵃⁱ[ℝ] E :=
    A.subtypeₐᵢ.comp translate.symm.toAffineIsometry
  have hvertex (i : s) : inclusion (b i) = (i : E) := by
    change (translate.symm (translate (vertices i)) : E) = (i : E)
    rw [translate.symm_apply_apply]

  have hface (i : s) : convexHull ℝ (b '' {j | j ≠ i}) =
      {x | (∀ j, 0 ≤ b.coord j x) ∧ b.coord i x = 0} := by
    ext x
    constructor
    · intro hx
      have hfull : x ∈ convexHull ℝ (range b) :=
        convexHull_mono (image_subset_range _ _) hx
      refine ⟨by simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hfull, ?_⟩
      have hz : convexHull ℝ (b '' {j | j ≠ i}) ⊆ (b.coord i) ⁻¹' ({0} : Set ℝ) := by
        apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i))
        rintro _ ⟨j, hj, rfl⟩
        exact b.coord_apply_ne hj.symm
      exact hz hx
    · rintro ⟨hpos, hzero⟩
      let J := Finset.univ.erase i
      have hz (j : s) (hj : j ∉ J) : b.coord j x = 0 := by
        have hji : j = i := by simpa [J] using hj
        simpa [hji] using hzero
      have hsum : ∑ j ∈ J, b.coord j x = 1 := by
        rw [Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => hz j hj)]
        exact b.sum_coord_apply_eq_one x
      have hpoint : ∑ j ∈ J, b.coord j x • b j = x := by
        calc
          _ = ∑ j, b.coord j x • b j := by
            apply Finset.sum_subset (Finset.subset_univ J)
            intro j _ hj
            rw [hz j hj, zero_smul]
          _ = x := b.linear_combination_coord_eq_self x
      have hmem := J.centerMass_mem_convexHull (fun j _ => hpos j)
        (show 0 < ∑ j ∈ J, b.coord j x by rw [hsum]; exact zero_lt_one)
        (fun j hj => mem_image_of_mem b
          (show j ∈ {j : s | j ≠ i} from (Finset.mem_erase.mp hj).1))
      rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hpoint] at hmem
  have hboundary : frontier (convexHull ℝ (range b)) =
      ⋃ i : s, convexHull ℝ (b '' {j | j ≠ i}) := by
    ext x
    rw [← closure_sdiff_interior, ((finite_range b).isCompact_convexHull ℝ).isClosed.closure_eq,
      b.interior_convexHull, b.convexHull_eq_nonneg_coord]
    simp_rw [hface]
    constructor
    · rintro ⟨hx, hnot⟩
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      exact mem_iUnion.mpr ⟨i, hx, le_antisymm (not_lt.mp hi) (hx i)⟩
    · intro hx
      obtain ⟨i, hpos, hzero⟩ := mem_iUnion.mp hx
      exact ⟨hpos, fun h => (ne_of_gt (h i)) hzero⟩
  have htop : affineSpan ℝ (convexHull ℝ (range b)) = ⊤ := by
    rw [affineSpan_convexHull, b.tot]
  have hintrinsic : intrinsicFrontier ℝ (convexHull ℝ (range b)) =
      frontier (convexHull ℝ (range b)) := by
    let B := affineSpan ℝ (convexHull ℝ (range b))
    have hzero : (0 : A.direction) ∈ B := by rw [show B = ⊤ from htop]; trivial
    let : Nonempty B := ⟨⟨0, hzero⟩⟩
    let e : B ≃ᵃⁱ[ℝ] A.direction := AffineIsometryEquiv.ofTop B htop
    change e.toHomeomorph '' frontier (e.toHomeomorph ⁻¹' convexHull ℝ (range b)) = _
    rw [e.toHomeomorph.image_frontier, e.toHomeomorph.image_preimage]
  have himage : inclusion '' convexHull ℝ (range b) = convexHull ℝ (s : Set E) := by
    change inclusion.toAffineMap '' convexHull ℝ (range b) = _
    rw [inclusion.toAffineMap.image_convexHull]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      change inclusion (b i) ∈ s
      rw [hvertex]
      exact i.property
    · intro hx
      exact ⟨b ⟨x, hx⟩, mem_range_self _, hvertex ⟨x, hx⟩⟩
  rw [← himage, inclusion.intrinsicFrontier_image, hintrinsic, hboundary, image_iUnion]
  apply iUnion_congr
  intro i
  change inclusion.toAffineMap '' convexHull ℝ (b '' {j | j ≠ i}) = _
  rw [inclusion.toAffineMap.image_convexHull, image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    change inclusion (b j) ∈ s.erase (i : E)
    rw [hvertex]
    exact Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩
  · intro hx
    obtain ⟨hxi, hxs⟩ := Finset.mem_erase.mp hx
    exact ⟨⟨x, hxs⟩, fun h => hxi (congrArg Subtype.val h), hvertex ⟨x, hxs⟩⟩


theorem simplex_intrinsicInterior_disjoint_face {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s t : Finset E)
    (hne : s.Nonempty) (hi : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊂ s) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
      (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨i, his, hit⟩ := Finset.exists_of_ssubset ht
  have hsub : t ⊆ s.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun h => hit (h ▸ hj), ht.subset hj⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [simplex_intrinsicFrontier s hne hi]
    exact mem_iUnion.mpr ⟨⟨i, his⟩, convexHull_mono hsub hy⟩
  rw [← intrinsicClosure_sdiff_intrinsicInterior] at hf
  exact hf.2 hx

end Poincare.Topology
