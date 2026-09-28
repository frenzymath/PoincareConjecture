import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarAlignedBall
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  {ι κ : Type*} [Finite ι] [Nonempty ι] [Finite κ]

theorem isFinitePLBallPair_closedStar_inter_halfspaces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hint : (0 : E) ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) (A : κ → E →ₗ[ℝ] ℝ)
    (hA : ∀ j, (K.link 0).RespectsAffineHyperplane (A j).toAffineMap)
    (hpositive : ∃ v : E, ∀ j, 0 < A j v) :
    IsFinitePLBallPair E
      ((K.closedStar 0).space ∩ {x | ∀ j, 0 ≤ A j x})
      {x | x ∈ (K.closedStar 0).space ∧ (∀ j, 0 ≤ A j x) ∧
        (x ∈ (K.link 0).space ∨ ∃ j, A j x = 0)} := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨C, _, H, hC, hcv, hC0, _, _, hH, hboundary, hmarks⟩ :=
    K.exists_finitePL_closedStar_chart_preserving_halfspaces hK hz hint c
  obtain ⟨v, hv⟩ := hpositive
  have hnonzero (j : κ) : A j ≠ 0 := by
    intro he
    have h := hv j
    rw [he, LinearMap.zero_apply] at h
    exact lt_irrefl _ h
  let Q : Set E := {x | ∀ j, 0 ≤ A j x}
  have hQclosed : IsClosed Q := by
    change IsClosed {x | ∀ j, 0 ≤ A j x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun j =>
      isClosed_le continuous_const (A j).continuous_of_finiteDimensional
  have hQcv : Convex ℝ Q := by
    change Convex ℝ {x | ∀ j, 0 ≤ A j x}
    simp only [ofPred_forall]
    exact convex_iInter fun j => (convex_Ici (0 : ℝ)).linear_preimage (A j)
  have hQint : interior Q = {x | ∀ j, 0 < A j x} := by
    have h := interior_finite_affine_halfspaces
      (fun j => -(A j).toAffineMap) (fun j => by simpa using hnonzero j)
    simpa only [Q, AffineMap.coe_neg, Pi.neg_apply, LinearMap.coe_toAffineMap,
      neg_nonpos, neg_lt_zero] using h
  let T := C ∩ Q
  have hT : IsCompact T := hC.inter_right hQclosed
  have hTint : interior T = interior C ∩ {x | ∀ j, 0 < A j x} := by
    change interior (C ∩ Q) = _
    rw [interior_inter, hQint]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hC0
  let r := ε / (‖v‖ + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  have hrv : r * ‖v‖ < ε := by
    change ε / (‖v‖ + 1) * ‖v‖ < ε
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hwC : r • v ∈ interior C := by
    apply hball
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact hrv
  have hne : (interior T).Nonempty := by
    refine ⟨r • v, hTint.symm.subset ⟨hwC, ?_⟩⟩
    intro j
    simpa only [map_smul, smul_eq_mul] using mul_pos hr (hv j)
  obtain ⟨g, ⟨J, hJ, hJC, hg⟩, hginv⟩ := hH.symm
  have hgfull : FinitePiecewiseAffineOn g C := ⟨J, hJ, hJC, hg⟩
  let F : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image (fun j => -(A j).toAffineMap)
  have hF : {x | ∀ f ∈ F, f x ≤ 0} = Q := by
    ext x
    simp only [F, Q, mem_ofPred_eq, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, AffineMap.coe_neg, Pi.neg_apply,
      LinearMap.coe_toAffineMap, neg_nonpos]
  obtain ⟨R, hR, hRs⟩ := J.exists_finite_triangulation_inter_halfspaces hJ F
  have hRT : R.space = T := by simpa only [hJC, hF] using hRs
  have hTball : IsFinitePLBallPair E T (frontier T) :=
    isFinitePLBallPair_of_compact_convex hT (hcv.inter hQcv) hne R hR hRT
  have hgin (x : E) (hx : x ∈ C) : g x ∈ (K.closedStar 0).space := by
    rw [← hginv ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hforward (x : E) (hx : x ∈ C) : (H ⟨g x, hgin x hx⟩ : E) = x := by
    have he : (⟨g x, hgin x hx⟩ : (K.closedStar 0).space) = H.symm ⟨x, hx⟩ :=
      Subtype.ext (hginv ⟨x, hx⟩).symm
    rw [he, H.apply_symm_apply]
  have hback (y : (K.closedStar 0).space) : g (H y) = y := by
    rw [← hginv (H y), H.symm_apply_apply]
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hginv] using hxy
    exact congrArg Subtype.val (H.symm.injective he)
  have hsource : g '' T = (K.closedStar 0).space ∩ Q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hgin x hx.1, ?_⟩
      intro j
      have h := (hmarks (A j) (hA j) ⟨g x, hgin x hx.1⟩).2
      rw [hforward x hx.1] at h
      exact h.mp (hx.2 j)
    · intro hy
      refine ⟨H ⟨y, hy.1⟩, ⟨(H ⟨y, hy.1⟩).property, ?_⟩, hback ⟨y, hy.1⟩⟩
      intro j
      exact ((hmarks (A j) (hA j) ⟨y, hy.1⟩).2).mpr (hy.2 j)
  have hfront (x : E) : x ∈ frontier T ↔
      x ∈ T ∧ (x ∈ frontier C ∨ ∃ j, A j x = 0) := by
    rw [frontier, hT.isClosed.closure_eq, hTint]
    change (x ∈ T ∧ ¬(x ∈ interior C ∧ ∀ j, 0 < A j x)) ↔ _
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      by_cases hi : x ∈ interior C
      · right
        obtain ⟨j, hj⟩ := not_forall.mp (fun h => hn ⟨hi, h⟩)
        exact ⟨j, le_antisymm (not_lt.mp hj) (hx.2 j)⟩
      · left
        rw [frontier, hC.isClosed.closure_eq]
        exact ⟨hx.1, hi⟩
    · rintro ⟨hx, hb | ⟨j, hj⟩⟩
      · exact ⟨hx, fun hi => hb.2 hi.1⟩
      · refine ⟨hx, fun hi => ?_⟩
        have h := hi.2 j
        rw [hj] at h
        exact lt_irrefl _ h
  have hrim : g '' frontier T =
      {x | x ∈ (K.closedStar 0).space ∧ (∀ j, 0 ≤ A j x) ∧
        (x ∈ (K.link 0).space ∨ ∃ j, A j x = 0)} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxT, hxmark⟩ := (hfront x).mp hx
      have hy := hsource.subset (mem_image_of_mem g hxT)
      refine ⟨hy.1, hy.2, ?_⟩
      rcases hxmark with hxC | ⟨j, hj⟩
      · left
        apply (hboundary ⟨g x, hgin x hxT.1⟩).mpr
        rwa [hforward x hxT.1]
      · right
        refine ⟨j, ?_⟩
        have h := (hmarks (A j) (hA j) ⟨g x, hgin x hxT.1⟩).1
        rw [hforward x hxT.1] at h
        exact h.mp hj
    · rintro ⟨hyS, hyQ, hyb⟩
      let z : (K.closedStar 0).space := ⟨y, hyS⟩
      refine ⟨H z, (hfront _).mpr ⟨⟨(H z).property, ?_⟩, ?_⟩, hback z⟩
      · intro j
        exact ((hmarks (A j) (hA j) z).2).mpr (hyQ j)
      · rcases hyb with hyb | ⟨j, hj⟩
        · exact Or.inl ((hboundary z).mp hyb)
        · exact Or.inr ⟨j, ((hmarks (A j) (hA j) z).1).mpr hj⟩
  have hresult := hTball.image_of_subset hgfull (show T ⊆ C from inter_subset_left) hginj
  simpa only [hsource, hrim] using hresult

end Geometry.SimplicialComplex
