import PoincareConjecture.Proofs.M76.PrimeReduction.ClosedStarSectionChart
import PoincareConjecture.Proofs.M76.Mathlib.SmallClosedStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {ι : Type*} [Finite ι] [Nonempty ι]

theorem exists_finitePL_closedStar_half_body
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (A : E →ₗ[ℝ] ℝ)
    (v : E) (hv : 0 < A v)
    (hside : K.space ⊆ {x | 0 ≤ A x})
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hhalf : U ∩ {x | 0 ≤ A x} ⊆ K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E)
      (H : (K.closedStar 0).space ≃ₜ (C ∩ {x | 0 ≤ A x} : Set E)),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧
      (∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.space = C) ∧
      IsFinitePLBallPair E (K.closedStar 0).space
        ((K.link 0).space ∪ ((K.closedStar 0).space ∩ {x | A x = 0})) ∧
      H.IsFinitePL ∧
      (∀ x : (K.closedStar 0).space,
        (x : E) ∈ (K.link 0).space ↔ (H x : E) ∈ frontier C) ∧
      ∀ x : (K.closedStar 0).space, A (H x : E) = 0 ↔ A (x : E) = 0 := by
  classical
  obtain ⟨C, L, _, hC, hcv, hC0, hCU, hdisj, hlocal, hL, hrep, _, _⟩ :=
    K.exists_small_closedStar_halfspace_neighborhood hK hz hU h0U c
  let : Fintype (ι ⊕ ι) := Fintype.ofFinite (ι ⊕ ι)
  let forms : Finset (E →ᵃ[ℝ] ℝ) :=
    Finset.univ.image (fun i => (L i).toAffineMap - AffineMap.const ℝ E 1)
  have hforms : C = {x | ∀ a ∈ forms, a x ≤ 0} := by
    rw [hrep]
    ext x
    constructor
    · intro hx a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact sub_nonpos.mpr (hx i)
    · intro hx i
      exact sub_nonpos.mp (hx _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hpoly := hC.exists_finite_triangulation_of_halfspaces forms hforms
  have hstarK : (K.closedStar 0).space ⊆ K.space :=
    space_subset_of_le (show K.closedStar 0 ≤ K from fun _ hs => hs.1)
  have hwhole : (K.closedStar 0).space ∩ C = C ∩ {x | 0 ≤ A x} := by
    apply Subset.antisymm
    · exact fun _ hx => ⟨hx.2, hside (hstarK hx.1)⟩
    · intro x hx
      exact hlocal.subset ⟨hhalf ⟨hCU hx.1, hx.2⟩, hx.1⟩
  have hA : A ≠ 0 := by
    intro he
    simp only [he, LinearMap.zero_apply, lt_self_iff_false] at hv
  let Q : Set E := {x | 0 ≤ A x}
  have hQclosed : IsClosed Q :=
    isClosed_le continuous_const A.continuous_of_finiteDimensional
  have hQcv : Convex ℝ Q := (convex_Ici (0 : ℝ)).linear_preimage A
  have hQint : interior Q = {x | 0 < A x} := by
    have h := (-A.toAffineMap).interior_nonpos (by simpa using hA)
    simpa only [Q, AffineMap.coe_neg, Pi.neg_apply,
      LinearMap.coe_toAffineMap, neg_nonpos, neg_lt_zero] using h
  let T := C ∩ Q
  have hT : IsCompact T := hC.inter_right hQclosed
  have hTint : interior T = interior C ∩ {x | 0 < A x} := by
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
  have hwA : 0 < A (r • v) := by
    simpa only [map_smul, smul_eq_mul] using mul_pos hr hv
  have hTi : (interior T).Nonempty :=
    ⟨r • v, hTint.symm.subset ⟨hwC, hwA⟩⟩
  have hwstar : r • v ∈ (K.closedStar 0).space :=
    (hwhole.symm.subset ⟨interior_subset hwC, hwA.le⟩).1
  have hwzero : r • v ≠ (0 : E) := by
    intro he
    simp only [he, map_zero, lt_self_iff_false] at hwA
  obtain ⟨z, hzlink, _, _, _⟩ := exists_linkPoint_smul hwstar hwzero
  have hne : (K.link 0).space.Nonempty := ⟨z, hzlink⟩
  obtain ⟨H, hH, hboundary, hmarks⟩ := K.exists_finitePL_closedStar_section_chart
    hK hz hne hC hcv hC0 hdisj L hL hrep
  have halign : (K.link 0).RespectsAffineHyperplane A.toAffineMap := by
    intro s hs
    right
    intro x hx
    exact hside (hstarK (space_subset_of_le (K.link_le_closedStar 0)
      ((K.link 0).convexHull_subset_space hs hx)))
  let G := H.trans (Homeomorph.setCongr hwhole)
  have hG : G.IsFinitePL := hH.setCongr rfl hwhole
  have hGb (x : (K.closedStar 0).space) :
      (x : E) ∈ (K.link 0).space ↔ (G x : E) ∈ frontier C := hboundary x
  have hGzero (x : (K.closedStar 0).space) :
      A (G x : E) = 0 ↔ A (x : E) = 0 := (hmarks A halign x).1
  have hfront (x : E) : x ∈ frontier T ↔
      x ∈ T ∧ (x ∈ frontier C ∨ A x = 0) := by
    rw [frontier, hT.isClosed.closure_eq, hTint]
    change (x ∈ T ∧ ¬(x ∈ interior C ∧ 0 < A x)) ↔ _
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      by_cases hi : x ∈ interior C
      · exact Or.inr (le_antisymm (not_lt.mp (fun hp => hn ⟨hi, hp⟩)) hx.2)
      · exact Or.inl ⟨hC.isClosed.closure_eq.symm ▸ hx.1, hi⟩
    · rintro ⟨hx, hb | hzA⟩
      · exact ⟨hx, fun hi => hb.2 hi.1⟩
      · exact ⟨hx, fun hi => (ne_of_gt hi.2) hzA⟩
  have hpair : IsFinitePLBallPair E (K.closedStar 0).space
      ((K.link 0).space ∪ ((K.closedStar 0).space ∩ {x | A x = 0})) := by
    refine ⟨union_subset (space_subset_of_le (K.link_le_closedStar 0))
      inter_subset_left, T, hT, hcv.inter hQcv, hTi, G, hG, ?_⟩
    intro x
    rw [hfront]
    constructor
    · intro hx
      refine ⟨(G x).property, ?_⟩
      rcases hx with hb | hxzero
      · exact Or.inl ((hGb x).mp hb)
      · exact Or.inr ((hGzero x).mpr hxzero.2)
    · rintro ⟨_, hb | hxzero⟩
      · exact Or.inl ((hGb x).mpr hb)
      · exact Or.inr ⟨x.property, (hGzero x).mp hxzero⟩
  exact ⟨C, G, hC, hcv, hC0, hpoly, hpair, hG, hGb, hGzero⟩

end Geometry.SimplicialComplex
