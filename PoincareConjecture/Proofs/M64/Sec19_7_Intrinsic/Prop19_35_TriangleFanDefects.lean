import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleRegularFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCornerFans





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in




theorem m64Intrinsic_triangle_region_fan_defects
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hreg0 : deriv base 0 ≠ 0) (hreg1 : deriv base D ≠ 0)
    (horth0 : g.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horth1 : g.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (hnorm0 : ‖base 0‖ = 1) (hnorm1 : ‖base D‖ = 1)
    (hinward0 : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinward1 : 0 < inner ℝ (base D) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 v1 vT : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = base 0) (hv1 : v1.1 = base D) (hvT : vT.1 = alpha A) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
    (∑ v : Euler.CoordinateVertex R.coordinates R.basis,
      ((if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
        coordinateVertexAngleContribution g R.coordinates R.basis v.1)) =
      2 * Real.pi - coordinateVertexAngleContribution g R.coordinates R.basis vT.1 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
  let defect (v : Euler.CoordinateVertex R.coordinates R.basis) :=
    (if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution g R.coordinates R.basis v.1
  change (∑ v, defect v) = _
  have hzero (v : Euler.CoordinateVertex R.coordinates R.basis)
      (h0 : v.1 ≠ base 0) (h1 : v.1 ≠ base D) (hT : v.1 ≠ alpha A) : defect v = 0 := by
    have hf := m64Intrinsic_triangle_region_regular_vertex_fan R g hc ha hb hci hai hbi
      hcreg hareg hbreg hstartA hstartB hmeet hbaseA hbaseB hsides hU hV hUV hfront hfV
      v h0 h1 hT
    simp only [defect, hf, sub_self]
  have hp0 : base 0 ∉ beta '' Icc 0 B := by
    rintro ⟨t, ht, he⟩
    exact hD.ne (hbaseB 0 ⟨le_rfl, hD.le⟩ t ht he.symm).1
  have hfan0 := m64Intrinsic_annular_normal_corner_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g hc ha hD hA hci hai hstartA.symm hreg0
    horth0 (isCompact_Icc.image hb.continuous) hp0 hU hV hUV
    (hfront.trans (by ac_rfl)) hfV hnorm0 hinward0 hsub R.cover v0 hv0
  have hri : InjOn (fun s => base (D - s)) (Icc 0 D) := by
    intro s hs t ht he
    have h := hci ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ he
    linarith
  have hrimage : (fun s => base (D - s)) '' Icc 0 D = base '' Icc 0 D := by
    change (base ∘ fun s => D - s) '' Icc 0 D = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_self, sub_zero]
  have hp1 : base (D - 0) ∉ alpha '' Icc 0 A := by
    rw [sub_zero]
    rintro ⟨t, ht, he⟩
    exact hD.ne' (hbaseA D ⟨hD.le, le_rfl⟩ t ht he.symm).1
  have hrd : deriv (fun s => base (D - s)) 0 = -deriv base D := by
    rw [deriv_comp_const_sub, sub_zero]
  have hrreg : deriv (fun s => base (D - s)) 0 ≠ 0 := by
    rw [hrd]
    exact neg_ne_zero.mpr hreg1
  have hrorth : g.inner (base (D - 0))
      (deriv (fun s => base (D - s)) 0 : AnnulusCoordinates)
      (deriv beta 0 : AnnulusCoordinates) = 0 := by
    rw [sub_zero, hrd, map_neg, neg_apply, horth1, neg_zero]
  have hrfront : frontier U = (fun s => base (D - s)) '' Icc 0 D ∪
      beta '' Icc 0 B ∪ alpha '' Icc 0 A := by
    rw [hrimage]
    exact hfront.trans (by ac_rfl)
  have hrc : ContDiff ℝ ∞ (fun s => base (D - s)) :=
    hc.comp (contDiff_const.sub contDiff_id)
  have hfan1 := m64Intrinsic_annular_normal_corner_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g
    hrc hb hD hB hri hbi
    (by simpa only [sub_zero] using hstartB.symm) hrreg hrorth
    (isCompact_Icc.image ha.continuous) hp1 hU hV hUV hrfront hfV
    (by simpa only [sub_zero] using hnorm1) (by simpa only [sub_zero] using hinward1)
    hsub R.cover v1 (by simpa only [sub_zero] using hv1)
  have hmem0 : v0.1 ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨0, ⟨le_rfl, hD.le⟩, hv0.symm⟩
  have hmem1 : v1.1 ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨D, ⟨hD.le, le_rfl⟩, hv1.symm⟩
  have hmemT : vT.1 ∈ frontier U := by
    rw [hfront]
    exact Or.inr (Or.inl ⟨A, ⟨hA.le, le_rfl⟩, hvT.symm⟩)
  have hd0 : defect v0 = Real.pi / 2 := by
    dsimp only [defect]
    rw [if_pos hmem0, hfan0]
    ring
  have hd1 : defect v1 = Real.pi / 2 := by
    dsimp only [defect]
    rw [if_pos hmem1, hfan1]
    ring
  have hdT : defect vT = Real.pi -
      coordinateVertexAngleContribution g R.coordinates R.basis vT.1 := by
    simp only [defect, if_pos hmemT]
  have hne01 : v0 ≠ v1 := by
    intro he
    have h := hci ⟨le_rfl, hD.le⟩ ⟨hD.le, le_rfl⟩
      (hv0.symm.trans ((congrArg Subtype.val he).trans hv1))
    exact hD.ne h
  have hne0T : v0 ≠ vT := by
    intro he
    have h := hbaseA 0 ⟨le_rfl, hD.le⟩ A ⟨hA.le, le_rfl⟩
      (hv0.symm.trans ((congrArg Subtype.val he).trans hvT))
    exact hA.ne' h.2
  have hne1T : v1 ≠ vT := by
    intro he
    have h := hbaseA D ⟨hD.le, le_rfl⟩ A ⟨hA.le, le_rfl⟩
      (hv1.symm.trans ((congrArg Subtype.val he).trans hvT))
    exact hD.ne' h.1
  have hsum : (∑ v, defect v) = ∑ v ∈ ({v0, v1, vT} : Finset _), defect v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    apply hzero
    · intro h
      exact hv (by simp only [Finset.mem_insert, Finset.mem_singleton]
                   exact Or.inl (Subtype.ext (h.trans hv0.symm)))
    · intro h
      exact hv (by simp only [Finset.mem_insert, Finset.mem_singleton]
                   exact Or.inr (Or.inl (Subtype.ext (h.trans hv1.symm))))
    · intro h
      exact hv (by simp only [Finset.mem_insert, Finset.mem_singleton]
                   exact Or.inr (Or.inr (Subtype.ext (h.trans hvT.symm))))
  rw [hsum, Finset.sum_insert (by simp [hne01, hne0T]), Finset.sum_pair hne1T,
    hd0, hd1, hdT]
  ring

end PoincareConjecture
