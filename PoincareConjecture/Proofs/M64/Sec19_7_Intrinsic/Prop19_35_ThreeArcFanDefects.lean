import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCornerFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalInteriorFans





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
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




theorem m64Intrinsic_three_arc_region_fan_defects_le
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    (hsreg : ∀ t ∈ Ioo (0 : ℝ) S, deriv sigma t ≠ 0)
    (hreg0 : deriv (gamma false) 0 ≠ 0)
    (horth : g.inner (gamma false 0) (deriv (gamma false) 0) (deriv sigma 0) = 0)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U) (hnorm : ‖gamma false 0‖ = 1)
    (hinward : 0 < inner ℝ (gamma false 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = gamma false 0) (hv1 : v1.1 = gamma true (T true)) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
    (∑ v : Euler.CoordinateVertex R.coordinates R.basis,
      ((if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
        coordinateVertexAngleContribution g R.coordinates R.basis v.1)) ≤
      3 * Real.pi / 2 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
  let defect (v : Euler.CoordinateVertex R.coordinates R.basis) :=
    (if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution g R.coordinates R.basis v.1
  change (∑ v, defect v) ≤ _
  have htrace : frontier (⋃ i, (R.face i).carrier) = frontier U := by
    rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2]
  have hregular_fan {eta : ℝ → AnnulusCoordinates} {a b p : ℝ}
      (he : ContDiff ℝ ∞ eta) (hei : InjOn eta (Icc a b)) (hp : p ∈ Ioo a b)
      (hr : deriv eta p ≠ 0) {K : Set AnnulusCoordinates} (hK : IsCompact K)
      (hpK : eta p ∉ K) (hf : frontier U = eta '' Icc a b ∪ K)
      (v : Euler.CoordinateVertex R.coordinates R.basis) (hv : v.1 = eta p) :
      coordinateVertexAngleContribution g R.coordinates R.basis v.1 = Real.pi :=
    m64Intrinsic_region_arc_boundary_fan R.face R.coordinates R.basis R.smooth
      R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
      R.intersections R.intersection_frontier g he hei hp hr hK hpK
      hU hV hUV hf hfV R.cover v hv
  have hzero (v : Euler.CoordinateVertex R.coordinates R.basis)
      (hvstart : v.1 ≠ gamma false 0) (hvend : v.1 ≠ gamma true (T true)) : defect v = 0 := by
    by_cases hvboundary : v.1 ∈ frontier U
    · have hfan : coordinateVertexAngleContribution g R.coordinates R.basis v.1 =
          Real.pi := by
        by_cases hvjoin : v.1 = gamma false (T false)
        · have hpK : gamma false (T false) ∉ sigma '' Icc 0 S := by
            rintro ⟨t, ht, he⟩
            exact (hT false).ne'
              (has (T false) ⟨(hT false).le, le_rfl⟩ t ht he.symm).1
          exact m64Intrinsic_straight_join_region_vertex_fan R.face R.coordinates R.basis
            R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
            R.intersections R.intersection_frontier g v (hg false) (hg true)
            (hT false) (hT true) hspeed (hinj false) (hinj true) hjoin hreg htan
            (isCompact_Icc.image hs.continuous) hpK hU hV hUV hfU hfV R.cover hvjoin
        · rw [hfU] at hvboundary
          rcases hvboundary with (hva | hvb) | hvs
          · obtain ⟨p, hp, hpv⟩ := hva
            have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
              hvstart (hpv.symm.trans (congrArg (gamma false) h.symm)))
            have hpT : p < T false := lt_of_le_of_ne hp.2 (fun h =>
              hvjoin (hpv.symm.trans (congrArg (gamma false) h)))
            have hpK : gamma false p ∉ gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S := by
              rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
              · exact hpT.ne (hab p hp t ht he.symm).1
              · exact hp0.ne' (has p hp t ht he.symm).1
            exact hregular_fan (hg false) (hinj false) ⟨hp0, hpT⟩
              (hregular false p ⟨hp0, hpT⟩)
              ((isCompact_Icc.image (hg true).continuous).union
                (isCompact_Icc.image hs.continuous)) hpK
              (hfU.trans (union_assoc _ _ _)) v hpv.symm
          · obtain ⟨p, hp, hpv⟩ := hvb
            have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
              hvjoin (hpv.symm.trans ((congrArg (gamma true) h.symm).trans hjoin.symm)))
            have hpT : p < T true := lt_of_le_of_ne hp.2 (fun h =>
              hvend (hpv.symm.trans (congrArg (gamma true) h)))
            have hpK : gamma true p ∉ gamma false '' Icc 0 (T false) ∪ sigma '' Icc 0 S := by
              rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
              · exact hp0.ne' (hab t ht p hp he).2
              · exact hpT.ne (hbs p hp t ht he.symm).1
            exact hregular_fan (hg true) (hinj true) ⟨hp0, hpT⟩
              (hregular true p ⟨hp0, hpT⟩)
              ((isCompact_Icc.image (hg false).continuous).union
                (isCompact_Icc.image hs.continuous)) hpK (hfU.trans (by ac_rfl)) v hpv.symm
          · obtain ⟨p, hp, hpv⟩ := hvs
            have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
              hvstart (hpv.symm.trans ((congrArg sigma h.symm).trans hstart)))
            have hpS : p < S := lt_of_le_of_ne hp.2 (fun h =>
              hvend (hpv.symm.trans ((congrArg sigma h).trans hend)))
            have hpK : sigma p ∉
                gamma false '' Icc 0 (T false) ∪ gamma true '' Icc 0 (T true) := by
              rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
              · exact hp0.ne' (has t ht p hp he).2
              · exact hpS.ne (hbs t ht p hp he).2
            exact hregular_fan hs hsi ⟨hp0, hpS⟩ (hsreg p ⟨hp0, hpS⟩)
              ((isCompact_Icc.image (hg false).continuous).union
                (isCompact_Icc.image (hg true).continuous)) hpK
              (hfU.trans (union_comm _ _)) v hpv.symm
      simp only [defect, if_pos hvboundary, hfan, sub_self]
    · have hvregion : v.1 ∈ ⋃ i, (R.face i).carrier := by
        obtain ⟨⟨i, k⟩, hik⟩ := v.2
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [R.carrier]
        exact ⟨R.basis i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
      have hvint : v.1 ∈ interior (⋃ i, (R.face i).carrier) := by
        by_contra h
        exact hvboundary (htrace ▸ ⟨subset_closure hvregion, h⟩)
      have hfan := m64Intrinsic_regional_interior_vertex_fan R.face R.coordinates R.basis
        R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
        R.intersections R.intersection_frontier g v hvint
      simp only [defect, if_neg hvboundary, hfan, sub_self]
  have hpW : gamma false 0 ∉ gamma true '' Icc 0 (T true) := by
    rintro ⟨t, ht, he⟩
    exact (hT false).ne (hab 0 ⟨le_rfl, (hT false).le⟩ t ht he.symm).1
  have hfan0 := m64Intrinsic_annular_normal_corner_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g (hg false) hs (hT false) hS
    (hinj false) hsi hstart hreg0 horth (isCompact_Icc.image (hg true).continuous)
    hpW hU hV hUV (hfU.trans (by ac_rfl)) hfV hnorm hinward hsub R.cover v0 hv0
  have hmem0 : v0.1 ∈ frontier U := by
    rw [hfU]
    exact Or.inl (Or.inl ⟨0, ⟨le_rfl, (hT false).le⟩, hv0.symm⟩)
  have hmem1 : v1.1 ∈ frontier U := by
    rw [hfU]
    exact Or.inl (Or.inr ⟨T true, ⟨(hT true).le, le_rfl⟩, hv1.symm⟩)
  have hdefect0 : defect v0 = Real.pi / 2 := by
    dsimp only [defect]
    rw [if_pos hmem0, hfan0]
    ring
  have hdefect1 : defect v1 ≤ Real.pi := by
    dsimp only [defect]
    rw [if_pos hmem1]
    exact sub_le_self _ (vertex_angle_nonneg g R.coordinates R.basis v1.1)
  have hne : v0 ≠ v1 := by
    intro h
    have he : sigma 0 = sigma S := hstart.trans (hv0.symm.trans
      ((congrArg Subtype.val h).trans (hv1.trans hend.symm)))
    exact hS.ne (hsi ⟨le_rfl, hS.le⟩ ⟨hS.le, le_rfl⟩ he)
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
