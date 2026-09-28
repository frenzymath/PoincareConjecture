import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_UpperGraph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_defining_function
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (phi : AnnulusCoordinates → ℝ) (ell : AnnulusCoordinates →L[ℝ] ℝ),
      HasFDerivAt phi ell (gamma p) ∧ phi (gamma p) = 0 ∧ ell ≠ 0 ∧
        (∀ᶠ z in 𝓝 (gamma p), z ∈ closure U ↔ 0 ≤ phi z) := by
  obtain ⟨L, h, S, x, hS, hx, hh, hcoord, hregion⟩ :=
    m64Intrinsic_exists_loop_upper_graph hg hend hinj hp hregular hU hV hdisj hfU hfV
  let X : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let Y : AnnulusCoordinates →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let phi := fun z => Y z - h (X z)
  let ell : AnnulusCoordinates →L[ℝ] ℝ := Y - deriv h x • X
  have hdh : HasDerivAt h (deriv h x) x :=
    ((hh x hx).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp) |>.hasDerivAt
  have hXbase : X (gamma p) = x := by
    change (L (gamma p)).1 = x
    rw [hcoord]
  have hYbase : Y (gamma p) = h x := by
    change (L (gamma p)).2 = h x
    rw [hcoord]
  have hd : HasFDerivAt phi ell (gamma p) := by
    exact Y.hasFDerivAt.sub
      (hdh.comp_hasFDerivAt_of_eq (gamma p) X.hasFDerivAt hXbase.symm)
  have hv : ell (L.symm (0, 1)) = 1 := by
    change (L (L.symm (0, 1))).2 - deriv h x * (L (L.symm (0, 1))).1 = 1
    rw [L.apply_symm_apply]
    simp
  have hell : ell ≠ 0 := by
    intro heq
    have hz : ell (L.symm (0, 1)) = 0 := by rw [heq]; rfl
    linarith
  refine ⟨phi, ell, hd, ?_, hell, ?_⟩
  · dsimp only [phi]
    rw [hXbase, hYbase, sub_self]
  · have ht : Tendsto L (𝓝 (gamma p)) (𝓝 (x, h x)) := by
      rw [← hcoord]
      exact L.continuous.tendsto _
    filter_upwards [ht.eventually hregion] with z hz
    change z ∈ closure U ↔ 0 ≤ (L z).2 - h (L z).1
    rw [sub_nonneg]
    simpa only [L.symm_apply_apply] using hz.1

theorem m64Intrinsic_return_region_smooth_boundary_fan
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
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hginj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (q : Euler.CoordinateVertex F b) (hq : q.1 = gamma p) :
    coordinateVertexAngleContribution g F b q.1 = Real.pi := by
  obtain ⟨phi, ell, hd, hzero, hell, hregion⟩ :=
    m64Intrinsic_exists_loop_defining_function hg hend hginj hp hregular hU hV hdisj hfU hfV
  apply m64Intrinsic_regional_boundary_vertex_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g q (hq.symm ▸ hd) (hq.symm ▸ hzero) hell
  simpa only [hq, hcover] using hregion

end PoincareConjecture
