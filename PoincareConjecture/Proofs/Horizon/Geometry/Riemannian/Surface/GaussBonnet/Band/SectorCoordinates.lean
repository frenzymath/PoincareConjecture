import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.SectorGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem topLineFunctional_horizontal (i : Fin B.interface.count) :
    (B.topLineFunctional i).linear (collarParameterEquiv.symm (1, 0)) =
      -(B.interface.piece i).linear 1 := by
  simp [topLineFunctional]

theorem topLineFunctional_pair_independent
    (i j : Fin B.interface.count)
    (hne : (B.interface.piece i).linear 1 ≠ (B.interface.piece j).linear 1) :
    LinearIndependent ℝ
      (![(B.topLineFunctional i).linear, (B.topLineFunctional j).linear] :
        Fin 2 → Module.Dual ℝ Plane) := by
  rw [linearIndependent_fin2]
  refine ⟨B.topLineFunctional_linear_ne_zero j, ?_⟩
  intro r he
  have hv := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (collarParameterEquiv.symm (0, 1))) he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    LinearMap.smul_apply, topLineFunctional_vertical, smul_eq_mul, mul_one] at hv
  have hh := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (collarParameterEquiv.symm (1, 0))) he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    LinearMap.smul_apply, topLineFunctional_horizontal, smul_eq_mul, hv, one_mul] at hh
  exact hne (neg_injective hh).symm

theorem topLineFunctional_eq_of_adjacent_slope_eq
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc)
    (he : (B.interface.piece i).linear 1 = (B.interface.piece j).linear 1) :
    B.topLineFunctional i = B.topLineFunctional j := by
  have hlin : (B.interface.piece i).linear = (B.interface.piece j).linear := by
    ext
    exact he
  have hpiece : B.interface.piece i = B.interface.piece j := AffineMap.ext_linear hlin
    (show B.interface.piece i (B.interface.cut i.succ) =
      B.interface.piece j (B.interface.cut i.succ) from by
      rw [(B.interface.piece_endpoints i).2, hij, (B.interface.piece_endpoints j).1])
  simp only [topLineFunctional, hpiece]

theorem exists_internal_top_sector_coordinates
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc)
    (hne : (B.interface.piece i).linear 1 ≠ (B.interface.piece j).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.planarTopVertex i.succ ∧
      c.coord 1 = B.topLineFunctional i ∧ c.coord 2 = B.topLineFunctional j := by
  apply exists_affineBasis_coords_of_independent_functionals
    (B.topLineFunctional i) (B.topLineFunctional j) (B.planarTopVertex i.succ)
  · exact B.topLineFunctional_right_vertex i
  · rw [planarTopVertex, hij]
    exact B.topLineFunctional_left_vertex j
  · exact B.topLineFunctional_pair_independent i j hne

theorem planar_carrier_internal_top_halfspace_of_slope_eq
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc)
    (he : (B.interface.piece i).linear 1 = (B.interface.piece j).linear 1) :
    F.symm '' B.carrier =ᶠ[𝓝 (B.planarTopVertex i.succ)]
      {z | B.topLineFunctional i z ≤ 0} := by
  have hfun := B.topLineFunctional_eq_of_adjacent_slope_eq i j hij he
  filter_upwards [B.planar_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ F.symm '' B.carrier ↔ B.topLineFunctional i z ≤ 0
  simpa only [he, le_refl, if_true, ← topLineFunctional_apply, hfun, or_self] using hz

theorem exists_internal_top_convex_sector_coordinates
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.interface.piece j).linear 1 < (B.interface.piece i).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.planarTopVertex i.succ ∧
      c.coord 1 = -B.topLineFunctional i ∧ c.coord 2 = -B.topLineFunctional j ∧
      F.symm '' B.carrier =ᶠ[𝓝 (B.planarTopVertex i.succ)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have hind := (B.topLineFunctional_pair_independent i j hslope.ne').neg
  have hneg : LinearIndependent ℝ
      (![(-B.topLineFunctional i).linear, (-B.topLineFunctional j).linear] :
        Fin 2 → Module.Dual ℝ Plane) := by
    convert! hind using 1
    ext k
    fin_cases k <;> rfl
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_affineBasis_coords_of_independent_functionals
    (-B.topLineFunctional i) (-B.topLineFunctional j) (B.planarTopVertex i.succ)
    (by change -(B.topLineFunctional i (B.planarTopVertex i.succ)) = 0
        rw [planarTopVertex, B.topLineFunctional_right_vertex i, neg_zero])
    (by change -(B.topLineFunctional j (B.planarTopVertex i.succ)) = 0
        rw [planarTopVertex, hij, B.topLineFunctional_left_vertex j, neg_zero]) hneg
  refine ⟨c, hc0, hc1, hc2, ?_⟩
  filter_upwards [B.planar_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ F.symm '' B.carrier ↔ 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z
  rw [hc1, hc2]
  change z ∈ F.symm '' B.carrier ↔ 0 ≤ -(B.topLineFunctional i z) ∧
    0 ≤ -(B.topLineFunctional j z)
  simpa only [not_le.mpr hslope, if_false, neg_nonneg, topLineFunctional_apply] using hz

theorem exists_internal_top_reflex_sector_coordinates
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.interface.piece i).linear 1 < (B.interface.piece j).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.planarTopVertex i.succ ∧
      c.coord 1 = B.topLineFunctional i ∧ c.coord 2 = B.topLineFunctional j ∧
      F.symm '' B.carrier =ᶠ[𝓝 (B.planarTopVertex i.succ)]
        {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  obtain ⟨c, hc0, hc1, hc2⟩ := B.exists_internal_top_sector_coordinates i j hij hslope.ne
  refine ⟨c, hc0, hc1, hc2, ?_⟩
  filter_upwards [B.planar_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ F.symm '' B.carrier ↔ c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0
  simpa only [hslope.le, if_true, hc1, hc2, topLineFunctional_apply] using hz

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
