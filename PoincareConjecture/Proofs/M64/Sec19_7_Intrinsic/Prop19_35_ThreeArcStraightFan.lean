import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinFan

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

namespace M64IntrinsicCoordinateTriangulation

theorem boundary_injective {K : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation K) (i : Fin R.count) (k : Fin 3) :
    InjOn ((R.face i).boundary k).map (Icc (0 : ℝ) 1) :=
  m64Intrinsic_coordinate_boundary_injective R.face R.coordinates R.basis
    R.source R.boundary i k

end M64IntrinsicCoordinateTriangulation

theorem m64Intrinsic_exists_three_arc_triangulation_with_straight_fan
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
    (hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U))
    (hray : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma e t + z • quarterTurn (deriv (gamma e) t) ∈ U) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 vj v1 : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = gamma false 0 ∧ vj.1 = gamma false (T false) ∧ v1.1 = gamma true (T true) ∧
        ∀ g : RiemannianMetric 2 AnnulusCoordinates,
          coordinateVertexAngleContribution g R.coordinates R.basis vj.1 = Real.pi := by
  obtain ⟨C, b, ⟨D⟩⟩ := m64Intrinsic_exists_three_arc_collar gamma sigma T hg hs hT hS hspeed
    hinj hsi hstart hend hjoin hreg htan hab has hbs hregular hsreg hind0 hind1
    hU hV hUV hfront hfV hray
  obtain ⟨R, v0, vj, v1, hv0, hvj, hv1⟩ := D.exists_triangulation hU hcompact hfront
  have hpK : gamma false (T false) ∉ sigma '' Icc 0 S := by
    rintro ⟨y, hy, he⟩
    exact (hT false).ne' (has (T false) ⟨(hT false).le, le_rfl⟩ y hy he.symm).1
  refine ⟨R, v0, vj, v1, hv0, hvj, hv1, ?_⟩
  intro g
  exact m64Intrinsic_straight_join_region_vertex_fan R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
    R.intersections R.intersection_frontier g vj (hg false) (hg true)
    (hT false) (hT true) hspeed (hinj false) (hinj true) hjoin hreg htan
    (isCompact_Icc.image hs.continuous) hpK hU hV hUV hfront hfV R.cover hvj

end PoincareConjecture
