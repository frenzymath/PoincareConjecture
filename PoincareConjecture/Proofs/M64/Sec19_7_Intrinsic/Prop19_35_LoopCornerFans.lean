import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalCornerFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerCoordinates













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture






theorem m64Intrinsic_return_region_corner_fan
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
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hginj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (q : Euler.CoordinateVertex F b) (hq : q.1 = gamma 0) :
    coordinateVertexAngleContribution g F b q.1 =
        g.cornerAngle (gamma 0) (deriv gamma 0) (-deriv gamma T) ∨
      coordinateVertexAngleContribution g F b q.1 =
        2 * Real.pi - g.cornerAngle (gamma 0) (deriv gamma 0) (-deriv gamma T) := by
  obtain ⟨phi, L, positive, hd, hzero, hu, hv, hregion⟩ :=
    m64Intrinsic_exists_loop_corner_coordinates hg hT hend hginj hind hU hV hdisj hfU hfV
  have hf := m64Intrinsic_regional_corner_vertex_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g q L (hq.symm ▸ hd) (hq.symm ▸ hzero) positive
      (by simpa only [hq, hcover] using hregion)
  rw [hq, hu, hv] at hf
  rw [hq]
  cases positive
  · exact Or.inr (by simpa only [Bool.false_eq_true, if_false] using hf)
  · exact Or.inl (by simpa only [if_true] using hf)

end PoincareConjecture
