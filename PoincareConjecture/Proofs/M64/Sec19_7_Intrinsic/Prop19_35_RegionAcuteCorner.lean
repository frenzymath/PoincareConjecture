import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCornerCoordinates
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalCornerFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_acute_two_arc_corner_coordinates
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {W : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U)
    (q : Euler.CoordinateVertex R.coordinates R.basis) (hq : q.1 = alpha 0)
    (hangle : coordinateVertexAngleContribution g R.coordinates R.basis q.1 < Real.pi) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha 0) ∧ phi (alpha 0) = 0 ∧
      L.symm (1, 0) = deriv alpha 0 ∧ L.symm (0, 1) = deriv beta 0 ∧
      (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  obtain ⟨phi, L, positive, hd, hzero, hu, hv, hregion⟩ :=
    m64Intrinsic_exists_two_arc_corner_coordinates ha hb hA hB hai hbi hbase hind
      hW hpW hU hV hUV hfU hfV
  have hfan := m64Intrinsic_regional_corner_vertex_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g q L (hq.symm ▸ hd) (hq.symm ▸ hzero)
    positive (by simpa only [hq, R.cover] using hregion)
  have hpos : positive = true := by
    cases positive
    · simp only [Bool.false_eq_true, if_false] at hfan
      have hle : g.cornerAngle q.1 (L.symm (1, 0)) (L.symm (0, 1)) ≤ Real.pi :=
        Real.arccos_le_pi _
      exfalso
      linarith
    · rfl
  refine ⟨phi, L, hd, hzero, hu, hv, ?_⟩
  simpa only [hpos, if_true] using hregion

end PoincareConjecture
