import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonRegularFans




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_coordinate_vertex_angle_nonneg
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




theorem m64Intrinsic_digon_fan_defects
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (v0 v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
    (∑ v : Euler.CoordinateVertex R.coordinates R.basis,
      ((if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
        coordinateVertexAngleContribution g R.coordinates R.basis v.1)) =
      2 * Real.pi - coordinateVertexAngleContribution g R.coordinates R.basis v0.1 -
        coordinateVertexAngleContribution g R.coordinates R.basis v1.1 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
  let defect (v : Euler.CoordinateVertex R.coordinates R.basis) :=
    (if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution g R.coordinates R.basis v.1
  change (∑ v, defect v) = _
  have hzero (v : Euler.CoordinateVertex R.coordinates R.basis)
      (h0 : v.1 ≠ alpha 0) (h1 : v.1 ≠ alpha A) : defect v = 0 := by
    have hf := m64Intrinsic_digon_regular_vertex_fan R g ha hb hai hbi hareg hbreg
      hbase hend hmeet hU hV hUV hfront hfV v h0 h1
    simp only [defect, hf, sub_self]
  have hmem0 : v0.1 ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨0, ⟨le_rfl, hA.le⟩, hv0.symm⟩
  have hmem1 : v1.1 ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨A, ⟨hA.le, le_rfl⟩, hv1.symm⟩
  have hne : v0 ≠ v1 := by
    intro h
    exact hA.ne (hai ⟨le_rfl, hA.le⟩ ⟨hA.le, le_rfl⟩
      (hv0.symm.trans ((congrArg Subtype.val h).trans hv1)))
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
  rw [hsum, Finset.sum_pair hne]
  simp only [defect, if_pos hmem0, if_pos hmem1]
  ring

end PoincareConjecture
