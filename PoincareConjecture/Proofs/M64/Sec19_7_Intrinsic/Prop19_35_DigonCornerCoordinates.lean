import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionAcuteCorner




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_digon_initial_convex_coordinates
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (v0 : Euler.CoordinateVertex R.coordinates R.basis) (hv0 : v0.1 = alpha 0)
    (hangle : coordinateVertexAngleContribution g R.coordinates R.basis v0.1 < Real.pi) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha 0) ∧ phi (alpha 0) = 0 ∧
      L.symm (1, 0) = deriv alpha 0 ∧ L.symm (0, 1) = deriv beta 0 ∧
      (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) ∧
      coordinateVertexAngleContribution g R.coordinates R.basis v0.1 =
        g.cornerAngle (alpha 0) (deriv alpha 0) (deriv beta 0) := by
  obtain ⟨phi, L, hd, hz, haL, hbL, hregion⟩ :=
    m64Intrinsic_exists_acute_two_arc_corner_coordinates R g ha hb hA hB hai hbi
      hbase hind isCompact_empty (notMem_empty (alpha 0)) hU hV hUV
      (by simpa only [union_empty] using hfront) hfV v0 hv0 hangle
  have hfan := m64Intrinsic_regional_corner_vertex_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g v0 L (hv0.symm ▸ hd) (hv0.symm ▸ hz)
    true (by simpa only [hv0, R.cover, if_true] using hregion)
  refine ⟨phi, L, hd, hz, haL, hbL, hregion, ?_⟩
  have hfan' : coordinateVertexAngleContribution g R.coordinates R.basis v0.1 =
      g.cornerAngle v0.1 (deriv alpha 0 : AnnulusCoordinates)
        (deriv beta 0 : AnnulusCoordinates) := by
    simpa only [if_true, haL, hbL] using hfan
  exact hfan'.trans (congrArg (fun p : AnnulusCoordinates =>
    g.cornerAngle p (deriv alpha 0 : AnnulusCoordinates)
      (deriv beta 0 : AnnulusCoordinates)) hv0)





theorem m64Intrinsic_digon_terminal_convex_coordinates
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hend : beta B = alpha A)
    (hind : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (v1 : Euler.CoordinateVertex R.coordinates R.basis) (hv1 : v1.1 = alpha A)
    (hangle : coordinateVertexAngleContribution g R.coordinates R.basis v1.1 < Real.pi) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha A) ∧ phi (alpha A) = 0 ∧
      L.symm (1, 0) = -deriv alpha A ∧ L.symm (0, 1) = -deriv beta B ∧
      (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) ∧
      coordinateVertexAngleContribution g R.coordinates R.basis v1.1 =
        g.cornerAngle (alpha A) (-deriv alpha A) (-deriv beta B) := by
  have reverse_inj {eta : ℝ → AnnulusCoordinates} {T : ℝ} (hi : InjOn eta (Icc 0 T)) :
      InjOn (fun t => eta (T - t)) (Icc 0 T) := by
    intro s hs t ht hst
    have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ hst
    linarith
  have reverse_image (eta : ℝ → AnnulusCoordinates) (T : ℝ) :
      (fun t => eta (T - t)) '' Icc 0 T = eta '' Icc 0 T := by
    change (eta ∘ fun t => T - t) '' Icc 0 T = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_self, sub_zero]
  have har : ContDiff ℝ ∞ (fun t => alpha (A - t)) :=
    ha.comp (contDiff_const.sub contDiff_id)
  have hbr : ContDiff ℝ ∞ (fun t => beta (B - t)) :=
    hb.comp (contDiff_const.sub contDiff_id)
  obtain ⟨phi, L, hd, hz, haL, hbL, hregion, hfan⟩ :=
    m64Intrinsic_digon_initial_convex_coordinates R g har hbr
      hA hB (reverse_inj hai) (reverse_inj hbi)
      (by simpa only [sub_zero] using hend)
      (by simpa only [deriv_comp_const_sub, sub_zero] using hind) hU hV hUV
      (by rw [reverse_image, reverse_image]; exact hfront) hfV v1
      (by simpa only [sub_zero] using hv1) hangle
  refine ⟨phi, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sub_zero] using hd
  · simpa only [sub_zero] using hz
  · simpa only [deriv_comp_const_sub, sub_zero] using haL
  · simpa only [deriv_comp_const_sub, sub_zero] using hbL
  · simpa only [sub_zero] using hregion
  · change coordinateVertexAngleContribution g R.coordinates R.basis v1.1 =
      g.cornerAngle (alpha (A - 0))
        (deriv (fun t => alpha (A - t)) 0 : AnnulusCoordinates)
        (deriv (fun t => beta (B - t)) 0 : AnnulusCoordinates) at hfan
    have hfan' : coordinateVertexAngleContribution g R.coordinates R.basis v1.1 =
        g.cornerAngle (alpha (A - 0)) (-deriv alpha A : AnnulusCoordinates)
          (-deriv beta B : AnnulusCoordinates) := by
      simpa only [deriv_comp_const_sub, sub_zero] using hfan
    exact hfan'.trans (congrArg (fun p : AnnulusCoordinates =>
      g.cornerAngle p (-deriv alpha A : AnnulusCoordinates)
        (-deriv beta B : AnnulusCoordinates)) (congrArg alpha (sub_zero A)))

end PoincareConjecture
