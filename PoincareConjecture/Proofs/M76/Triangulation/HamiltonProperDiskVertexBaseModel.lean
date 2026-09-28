import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineSectionFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

private theorem convex_section_model
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Finite ι]
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (L : ι → E →ₗ[ℝ] ℝ)
    (hrep : C = {x | ∀ i, L i x ≤ 1})
    (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F)
    (hleft : Function.LeftInverse r a) (ha0 : a 0 = 0) :
    IsCompact (a ⁻¹' C) ∧ Convex ℝ (a ⁻¹' C) ∧
      (0 : F) ∈ interior (a ⁻¹' C) ∧
      (∃ K : SimplicialComplex ℝ F, K.faces.Finite ∧ K.space = a ⁻¹' C) ∧
      IsFinitePLBallPair F (C ∩ range a) (frontier C ∩ range a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hright : LeftInvOn a r (range a) := by
    rintro x ⟨y, rfl⟩
    rw [hleft y]
  have hrange : range a = {x | a (r x) = x} := by
    ext x
    exact ⟨fun hx => hright hx, fun hx => ⟨r x, hx⟩⟩
  have hclosed : IsClosed (range a) := by
    rw [hrange]
    exact isClosed_eq (a.continuous.comp r.continuous) continuous_id
  have himage : r '' (C ∩ range a) = a ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a (r x) ∈ C
      rw [hright hx.2]
      exact hx.1
    · intro hy
      exact ⟨a y, ⟨hy, mem_range_self y⟩, hleft y⟩
  have hCp : IsCompact (a ⁻¹' C) := himage ▸ (hC.inter_right hclosed).image r.continuous
  have hcvp : Convex ℝ (a ⁻¹' C) := hcv.affine_preimage a.toAffineMap
  have hz : (0 : F) ∈ interior (a ⁻¹' C) := by
    apply preimage_interior_subset_interior_preimage a.continuous
    change a 0 ∈ interior C
    rwa [ha0]
  let forms : Finset (F →ᵃ[ℝ] ℝ) := Finset.univ.image
    (fun i => (L i).toAffineMap.comp a.toAffineMap - AffineMap.const ℝ F 1)
  have hforms : a ⁻¹' C = {x | ∀ A ∈ forms, A x ≤ 0} := by
    ext x
    simp only [mem_preimage, hrep, mem_ofPred_eq, forms, Finset.mem_image,
      Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      AffineMap.coe_sub, Pi.sub_apply, AffineMap.comp_apply, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, sub_nonpos]
    rfl
  obtain ⟨K, hK, hKs⟩ := hCp.exists_finite_triangulation_of_halfspaces forms hforms
  have hball := isFinitePLBallPair_of_compact_convex hCp hcvp ⟨0, hz⟩ K hK hKs
  have h := hball.affine_image a hleft.injective.injOn
  rw [a.frontier_preimage_convex hC.isClosed hcv ⟨0, ha0.symm ▸ hzero⟩,
    image_preimage_eq_inter_range, image_preimage_eq_inter_range] at h
  exact ⟨hCp, hcvp, hz, ⟨K, hK, hKs⟩, h⟩

local notation "P2" => (ℝ × ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)





theorem exists_convex_vertex_base_models {ι : Type*} [Finite ι]
    {C : Set V} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : V) ∈ interior C) (L : ι → V →ₗ[ℝ] ℝ)
    (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    IsFinitePLBallPair P2 (C ∩ {x | x.2 = 0})
      (frontier C ∩ {x | x.2 = 0}) ∧
    IsFinitePLBallPair P2 (C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1})
      ((frontier C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1}) ∪
        (C ∩ {x | x.2 = 0 ∧ x.1.1 = 0})) ∧
    ∃ q0 q1 : V, q0 ≠ q1 ∧
      IsFinitePLBallPair ℝ (C ∩ {x | x.2 = 0 ∧ x.1.1 = 0}) {q0, q1} ∧
      IsFinitePLBallPair ℝ (frontier C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1}) {q0, q1} ∧
      (C ∩ {x | x.2 = 0 ∧ x.1.1 = 0}) ∩
        (frontier C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1}) = {q0, q1} := by
  classical
  let a : P2 →ᴬ[ℝ] V :=
    ((ContinuousLinearMap.id ℝ P2).prod (0 : P2 →L[ℝ] ℝ)).toContinuousAffineMap
  let r := (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  have hleft : Function.LeftInverse r a := fun _ => rfl
  have ha0 : a 0 = 0 := rfl
  have harange : range a = {x : V | x.2 = 0} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
  let C0 := a ⁻¹' C
  obtain ⟨hC0, hcv0, hz0, ⟨K, hK, hKs⟩, hfull⟩ :=
    convex_section_model hC hcv hzero L hrep a r hleft ha0
  rw [harange] at hfull
  have hfront0 : frontier C0 = a ⁻¹' frontier C :=
    a.frontier_preimage_convex hC.isClosed hcv ⟨0, ha0.symm ▸ hzero⟩
  let A : P2 →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ
  have hAne : A ≠ 0 := by
    intro he
    have h := congrArg (fun f : P2 →ₗ[ℝ] ℝ => f (1, 0)) he
    exact one_ne_zero h
  have hhalfint : interior {x : P2 | 0 ≤ x.1} = {x | 0 < x.1} := by
    have h := (-A.toAffineMap).interior_nonpos (by simpa using hAne)
    simpa only [AffineMap.coe_neg, Pi.neg_apply, LinearMap.coe_toAffineMap,
      A, LinearMap.fst_apply, neg_nonpos, neg_lt_zero] using h
  obtain ⟨epsilon, hepsilon, hsmall⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hz0
  have hpos : (epsilon / 2, 0) ∈ interior C0 := by
    apply hsmall
    rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨by simpa only [Real.norm_eq_abs, abs_of_pos (half_pos hepsilon)] using
      half_lt_self hepsilon, by simpa using hepsilon⟩
  have hneg : (-epsilon / 2, 0) ∈ interior C0 := by
    apply hsmall
    rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    constructor
    · rw [Real.norm_eq_abs, neg_div, abs_neg, abs_of_pos (half_pos hepsilon)]
      exact half_lt_self hepsilon
    · simpa using hepsilon
  let Cplus : Set P2 := C0 ∩ {x | 0 ≤ x.1}
  have hCp : IsCompact Cplus := hC0.inter_right
    (isClosed_le continuous_const continuous_fst)
  have hcvp : Convex ℝ Cplus := hcv0.inter ((convex_Ici (0 : ℝ)).linear_preimage A)
  have hCpint : interior Cplus = interior C0 ∩ {x | 0 < x.1} := by
    change interior (C0 ∩ {x | 0 ≤ x.1}) = _
    rw [interior_inter, hhalfint]
  have hCpne : (interior Cplus).Nonempty :=
    ⟨(epsilon / 2, 0), hCpint.symm.subset ⟨hpos, half_pos hepsilon⟩⟩
  obtain ⟨Kplus, hKplus, hKpluss⟩ :=
    K.exists_finite_triangulation_inter_halfspaces hK {(-A).toAffineMap}
  have hKp : Kplus.space = Cplus := by
    rw [hKpluss, hKs]
    ext x
    simp only [Cplus, C0, mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton,
      forall_eq, LinearMap.coe_toAffineMap, LinearMap.neg_apply, A,
      LinearMap.fst_apply, neg_nonpos]
  have hplus := isFinitePLBallPair_of_compact_convex hCp hcvp hCpne Kplus hKplus hKp
  have hfrontplus : frontier Cplus = (frontier C0 ∩ {x | 0 ≤ x.1}) ∪
      (C0 ∩ {x | x.1 = 0}) := by
    rw [frontier, hCp.isClosed.closure_eq, hCpint]
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hi : x ∈ interior C0
      · right
        exact ⟨hx.1, le_antisymm (not_lt.mp (fun h => hn ⟨hi, h⟩)) hx.2⟩
      · exact Or.inl ⟨⟨hC0.isClosed.closure_eq.symm.subset hx.1, hi⟩, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨⟨hC0.isClosed.frontier_subset hx.1, hx.2⟩, fun hi => hx.1.2 hi.1⟩
      · exact ⟨⟨hx.1, hx.2.ge⟩, fun hi => (lt_irrefl (0 : ℝ)) (hx.2 ▸ hi.2)⟩
  have hcutimage : a '' Cplus = C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, rfl, hy.2⟩
    · intro hx
      refine ⟨x.1, ⟨?_, hx.2.2⟩, Prod.ext rfl hx.2.1.symm⟩
      change (x.1, 0) ∈ C
      rw [show ((x.1, 0) : V) = x from Prod.ext rfl hx.2.1.symm]
      exact hx.1
  have hcapimage : a '' (frontier C0 ∩ {x | 0 ≤ x.1}) =
      frontier C ∩ {x | x.2 = 0 ∧ 0 ≤ x.1.1} := by
    rw [hfront0]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, rfl, hy.2⟩
    · intro hx
      refine ⟨x.1, ⟨?_, hx.2.2⟩, Prod.ext rfl hx.2.1.symm⟩
      change (x.1, 0) ∈ frontier C
      rw [show ((x.1, 0) : V) = x from Prod.ext rfl hx.2.1.symm]
      exact hx.1
  have haxisimage : a '' (C0 ∩ {x | x.1 = 0}) =
      C ∩ {x | x.2 = 0 ∧ x.1.1 = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, rfl, hy.2⟩
    · intro hx
      refine ⟨x.1, ⟨?_, hx.2.2⟩, Prod.ext rfl hx.2.1.symm⟩
      change (x.1, 0) ∈ C
      rw [show ((x.1, 0) : V) = x from Prod.ext rfl hx.2.1.symm]
      exact hx.1
  have haxisfront : a '' (frontier C0 ∩ {x | x.1 = 0}) =
      frontier C ∩ {x | x.2 = 0 ∧ x.1.1 = 0} := by
    rw [hfront0]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, rfl, hy.2⟩
    · intro hx
      refine ⟨x.1, ⟨?_, hx.2.2⟩, Prod.ext rfl hx.2.1.symm⟩
      change (x.1, 0) ∈ frontier C
      rw [show ((x.1, 0) : V) = x from Prod.ext rfl hx.2.1.symm]
      exact hx.1
  have hplusimage := hplus.affine_image a hleft.injective.injOn
  rw [hcutimage, hfrontplus, image_union, hcapimage, haxisimage] at hplusimage
  have hcap := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK hC0 hcv0
    hKs A.toAffineMap ⟨(-epsilon / 2, 0), hneg, by change -epsilon / 2 < 0; linarith⟩
      ⟨0, hz0, rfl⟩ (by simp [Module.finrank_prod])
  have hcap3 := hcap.affine_image a hleft.injective.injOn
  change IsFinitePLBallPair ℝ (a '' (frontier C0 ∩ {x | 0 ≤ x.1}))
    (a '' (frontier C0 ∩ {x | x.1 = 0})) at hcap3
  rw [hcapimage, haxisfront] at hcap3
  let axis : ℝ →ᴬ[ℝ] V :=
    (((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)).prod
      (0 : ℝ →L[ℝ] ℝ)).toContinuousAffineMap
  let axisRet : V →ᴬ[ℝ] ℝ := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap
  have haxisrange : range axis = {x : V | x.2 = 0 ∧ x.1.1 = 0} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨rfl, rfl⟩
    · intro hx
      exact ⟨x.1.2, Prod.ext (Prod.ext hx.2.symm rfl) hx.1.symm⟩
  obtain ⟨_, _, _, _, haxis⟩ := convex_section_model hC hcv hzero L hrep axis axisRet
    (fun _ => rfl) rfl
  rw [haxisrange] at haxis
  obtain ⟨q0, q1, hq, hboundary⟩ := haxis.exists_boundary_eq_pair
  refine ⟨hfull, hplusimage, q0, q1, hq, ?_, ?_, ?_⟩
  · rwa [hboundary] at haxis
  · rwa [hboundary] at hcap3
  · rw [← hboundary]
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1.2⟩
    · intro hx
      exact ⟨⟨hC.isClosed.frontier_subset hx.1, hx.2⟩, hx.1, hx.2.1, hx.2.2.ge⟩

end PoincareConjecture.M76.HamiltonIndexOne
