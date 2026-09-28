import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerAnnularSide
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalCornerFans













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_annular_normal_corner_fan
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
    (hbase : beta 0 = alpha 0) (hareg : deriv alpha 0 ≠ 0)
    (horth : g.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (q : Euler.CoordinateVertex F b) (hq : q.1 = alpha 0) :
    coordinateVertexAngleContribution g F b q.1 = Real.pi / 2 := by
  have hbreg : deriv beta 0 ≠ 0 := by
    intro h
    simp only [h, inner_zero_right, lt_self_iff_false] at hinward
  have hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates) := by
    rw [linearIndependent_fin2]
    refine ⟨hbreg, ?_⟩
    intro a heq
    change a • deriv beta 0 = deriv alpha 0 at heq
    have hbb := g.pos (alpha 0) (deriv beta 0) hbreg
    have hp := horth
    rw [← heq, map_smul, smul_apply, smul_eq_mul] at hp
    have ha0 : a = 0 := (mul_eq_zero.mp hp).resolve_right hbb.ne'
    apply hareg
    simpa only [ha0, zero_smul] using heq.symm
  obtain ⟨phi, L, hd, hzero, hu, hv, hregion⟩ :=
    m64Intrinsic_exists_annular_two_arc_corner_coordinates ha hb hA hB hai hbi hbase hind
      hW hpW hU hV hdisj hfU hfV hnorm hinward hsub
  have hf := m64Intrinsic_regional_corner_vertex_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g q L (hq.symm ▸ hd) (hq.symm ▸ hzero) true
      (by simpa only [hq, hcover, if_true] using hregion)
  simp only [if_true, hu, hv, hq] at hf
  rw [hq] at hf
  rw [hq]
  apply hf.trans
  simp only [RiemannianMetric.cornerAngle, map_smul, smul_apply, smul_eq_mul,
    horth, mul_zero, Real.arccos_zero]

end PoincareConjecture
