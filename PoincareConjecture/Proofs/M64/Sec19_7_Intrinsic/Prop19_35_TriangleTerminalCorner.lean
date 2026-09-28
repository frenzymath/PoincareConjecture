import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionAcuteCorner





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem reverse_inj {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hi : InjOn gamma (Icc 0 T)) : InjOn (fun s => gamma (T - s)) (Icc 0 T) := by
  intro s hs t ht he
  have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
    ⟨by linarith [ht.2], by linarith [ht.1]⟩ he
  linarith

private theorem reverse_image (gamma : ℝ → AnnulusCoordinates) (T : ℝ) :
    (fun s => gamma (T - s)) '' Icc 0 T = gamma '' Icc 0 T := by
  change (gamma ∘ fun s => T - s) '' Icc 0 T = _
  rw [image_comp, image_const_sub_Icc]
  simp only [sub_self, sub_zero]





theorem m64Intrinsic_triangle_terminal_convex_coordinates
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hindT : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (vT : Euler.CoordinateVertex R.coordinates R.basis) (hvT : vT.1 = alpha A)
    (hangle : coordinateVertexAngleContribution g R.coordinates R.basis vT.1 < Real.pi) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha A) ∧ phi (alpha A) = 0 ∧
      L.symm (1, 0) = -deriv alpha A ∧ L.symm (0, 1) = -deriv beta B ∧
      (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  have har : ContDiff ℝ ∞ (fun s => alpha (A - s)) :=
    ha.comp (contDiff_const.sub contDiff_id)
  have hbr : ContDiff ℝ ∞ (fun s => beta (B - s)) :=
    hb.comp (contDiff_const.sub contDiff_id)
  have hbase : beta (B - 0) = alpha (A - 0) := by
    simpa only [sub_zero] using hmeet.symm
  have hind : LinearIndependent ℝ
      (![deriv (fun s => alpha (A - s)) 0, deriv (fun s => beta (B - s)) 0] :
        Fin 2 → AnnulusCoordinates) := by
    simpa only [deriv_comp_const_sub, sub_zero] using hindT
  have hpW : alpha (A - 0) ∉ base '' Icc 0 D := by
    rw [sub_zero]
    rintro ⟨s, hs, he⟩
    exact hA.ne' (hbaseA s hs A ⟨hA.le, le_rfl⟩ he).2
  have hrfront : frontier U = (fun s => alpha (A - s)) '' Icc 0 A ∪
      (fun s => beta (B - s)) '' Icc 0 B ∪ base '' Icc 0 D := by
    rw [reverse_image, reverse_image]
    exact hfront.trans (by ac_rfl)
  obtain ⟨phi, L, hd, hz, hu, hv, hr⟩ := m64Intrinsic_exists_acute_two_arc_corner_coordinates
    R g har hbr hA hB (reverse_inj hai) (reverse_inj hbi) hbase hind
    (isCompact_Icc.image hc.continuous) hpW hU hV hUV hrfront hfV vT
    (by simpa only [sub_zero] using hvT) hangle
  refine ⟨phi, L, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sub_zero] using hd
  · simpa only [sub_zero] using hz
  · simpa only [deriv_comp_const_sub, sub_zero] using hu
  · simpa only [deriv_comp_const_sub, sub_zero] using hv
  · simpa only [sub_zero] using hr

end PoincareConjecture
