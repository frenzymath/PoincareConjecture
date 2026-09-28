import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcInitialFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalInteriorFans

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem vertex_angle_nonneg
    {I : Type*} [Fintype I] (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates) (q : AnnulusCoordinates) :
    0 ≤ coordinateVertexAngleContribution g F b q := by
  unfold coordinateVertexAngleContribution
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact Real.arccos_nonneg _
  · exact le_rfl

open Classical in

theorem m64Intrinsic_two_arc_region_fan_defects_le
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (ha0 : deriv alpha 0 ≠ 0)
    (hareg : ∀ p ∈ Ioo (0 : ℝ) A, deriv alpha p ≠ 0)
    (hbreg : ∀ p ∈ Ioo (0 : ℝ) B, deriv beta p ≠ 0)
    (horth : g.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (v0 v1 : Euler.CoordinateVertex F b) (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∑ v : Euler.CoordinateVertex F b,
      ((if v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B then Real.pi else 2 * Real.pi) -
        coordinateVertexAngleContribution g F b v.1)) ≤ 3 * Real.pi / 2 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let defect (v : Euler.CoordinateVertex F b) :=
    (if v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution g F b v.1
  change (∑ v, defect v) ≤ _
  have htrace : frontier (⋃ i, (face i).carrier) =
      alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
    rw [hcover, (m64Intrinsic_jordan_interior_closure hU hV hdisj hfV.symm).2, hfU]
  have hzero (v : Euler.CoordinateVertex F b)
      (hvstart : v.1 ≠ alpha 0) (hvend : v.1 ≠ alpha A) : defect v = 0 := by
    by_cases hvboundary : v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B
    · rcases hvboundary with hvalpha | hvbeta
      · obtain ⟨p, hp, hpv⟩ := hvalpha
        have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
          hvstart (hpv.symm.trans (congrArg alpha h.symm)))
        have hpA : p < A := lt_of_le_of_ne hp.2 (fun h =>
          hvend (hpv.symm.trans (congrArg alpha h)))
        have hpK : alpha p ∉ beta '' Icc 0 B := by
          rintro ⟨t, ht, htp⟩
          rcases hmeet p hp t ht htp.symm with h | h
          · exact hp0.ne' h.1
          · exact hpA.ne h.1
        have hfan := m64Intrinsic_region_arc_boundary_fan face F b hF hFi hsource
          hcarrier hboundary hinj hinter hfront g ha hai ⟨hp0, hpA⟩ (hareg p ⟨hp0, hpA⟩)
          (isCompact_Icc.image hb.continuous) hpK hU hV hdisj hfU hfV hcover v hpv.symm
        have hmem : v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B := Or.inl ⟨p, hp, hpv⟩
        simp only [defect, if_pos hmem, hfan, sub_self]
      · obtain ⟨p, hp, hpv⟩ := hvbeta
        have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
          hvstart (hpv.symm.trans ((congrArg beta h.symm).trans hbase)))
        have hpB : p < B := lt_of_le_of_ne hp.2 (fun h =>
          hvend (hpv.symm.trans ((congrArg beta h).trans hend)))
        have hpK : beta p ∉ alpha '' Icc 0 A := by
          rintro ⟨t, ht, htp⟩
          rcases hmeet t ht p hp htp with h | h
          · exact hp0.ne' h.2
          · exact hpB.ne h.2
        have hfU' : frontier U = beta '' Icc 0 B ∪ alpha '' Icc 0 A :=
          hfU.trans (union_comm _ _)
        have hfan := m64Intrinsic_region_arc_boundary_fan face F b hF hFi hsource
          hcarrier hboundary hinj hinter hfront g hb hbi ⟨hp0, hpB⟩ (hbreg p ⟨hp0, hpB⟩)
          (isCompact_Icc.image ha.continuous) hpK hU hV hdisj hfU' hfV hcover v hpv.symm
        have hmem : v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B := Or.inr ⟨p, hp, hpv⟩
        simp only [defect, if_pos hmem, hfan, sub_self]
    · have hvregion : v.1 ∈ ⋃ i, (face i).carrier := by
        obtain ⟨⟨i, k⟩, hik⟩ := v.2
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [hcarrier]
        exact ⟨b i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
      have hvint : v.1 ∈ interior (⋃ i, (face i).carrier) := by
        by_contra h
        exact hvboundary (htrace ▸ ⟨subset_closure hvregion, h⟩)
      have hfan := m64Intrinsic_regional_interior_vertex_fan face F b hF hFi hsource
        hcarrier hboundary hinj hinter hfront g v hvint
      simp only [defect, if_neg hvboundary, hfan, sub_self]
  have hfan0 := m64Intrinsic_two_arc_initial_normal_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g ha hb hA hB hai hbi hbase ha0 horth hU hV hdisj
    hfU hfV hnorm hinward hsub hcover v0 hv0
  have hmem0 : v0.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B :=
    Or.inl ⟨0, ⟨le_rfl, hA.le⟩, hv0.symm⟩
  have hmem1 : v1.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B :=
    Or.inl ⟨A, ⟨hA.le, le_rfl⟩, hv1.symm⟩
  have hdefect0 : defect v0 = Real.pi / 2 := by
    dsimp only [defect]
    rw [if_pos hmem0, hfan0]
    ring
  have hdefect1 : defect v1 ≤ Real.pi := by
    dsimp only [defect]
    rw [if_pos hmem1]
    exact sub_le_self _ (vertex_angle_nonneg g F b v1.1)
  have hne : v0 ≠ v1 := by
    intro h
    have heq : alpha 0 = alpha A := hv0.symm.trans ((congrArg Subtype.val h).trans hv1)
    exact hA.ne (hai ⟨le_rfl, hA.le⟩ ⟨hA.le, le_rfl⟩ heq)
  have hsum : (∑ v, defect v) = ∑ v ∈ ({v0, v1} : Finset _), defect v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    apply hzero
    · intro h
      exact hv (Finset.mem_insert.mpr (Or.inl (Subtype.ext (h.trans hv0.symm))))
    · intro h
      exact hv (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_singleton.mpr (Subtype.ext (h.trans hv1.symm)))))
  rw [hsum, Finset.sum_pair hne, hdefect0]
  linarith

end PoincareConjecture
