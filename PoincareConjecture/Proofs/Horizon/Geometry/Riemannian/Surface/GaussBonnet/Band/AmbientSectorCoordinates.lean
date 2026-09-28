import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.SectorCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ChainSectorGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Monochromatic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapChordHalfspaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreBandRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Meshes
namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

noncomputable def ambientTopFunctional (i : Fin B.faces.interface.count) : Plane →ᵃ[ℝ] ℝ :=
  (B.faces.topLineFunctional i).comp
    (G.frame.trans collarParameterEquiv.symm).toContinuousLinearMap.toLinearMap.toAffineMap
theorem ambientTopFunctional_vertical (i : Fin B.faces.interface.count) :
    (B.ambientTopFunctional i).linear (G.frame.symm (0,1)) = 1 := by
  simpa [ambientTopFunctional] using B.faces.topLineFunctional_vertical i
theorem ambientTopFunctional_left_vertex (i : Fin B.faces.interface.count) :
    B.ambientTopFunctional i (B.chartTopVertex i.castSucc) = 0 := by
  simpa [ambientTopFunctional, chartTopVertex] using B.faces.topLineFunctional_left_vertex i
theorem ambientTopFunctional_right_vertex (i : Fin B.faces.interface.count) :
    B.ambientTopFunctional i (B.chartTopVertex i.succ) = 0 := by
  simpa [ambientTopFunctional, chartTopVertex] using B.faces.topLineFunctional_right_vertex i
theorem ambientTopFunctional_surjective (i : Fin B.faces.interface.count) :
    Function.Surjective (B.ambientTopFunctional i) := by
  intro r
  refine ⟨r • G.frame.symm (0,1) + B.chartTopVertex i.castSucc, ?_⟩
  have h := (B.ambientTopFunctional i).map_vadd (B.chartTopVertex i.castSucc) (r • G.frame.symm (0,1))
  simpa only [vadd_eq_add, map_smul, ambientTopFunctional_vertical, smul_eq_mul,
    mul_one, ambientTopFunctional_left_vertex, add_zero] using h

theorem ambientTopFunctional_eq_smul_topSupportingLine (i : Fin B.faces.interface.count) :
    ∃ r : ℝ, r ≠ 0 ∧ B.ambientTopFunctional i = r • B.topSupportingLine i := by
  let q := B.chartTopVertex i.castSucc
  let p := B.chartTopVertex i.succ
  have hne : p - q ≠ 0 := by
    intro he
    have hh := congrArg (fun z : Plane => (G.frame z).1) (sub_eq_zero.mp he)
    simp only [p,q,chartTopVertex,G.frame.apply_symm_apply] at hh
    exact (B.faces.interface.cut_strictMono Fin.castSucc_lt_succ).ne hh.symm
  have hq := (B.topSupportingLine_spec i).2 (left_mem_segment ℝ q p)
  have hp := (B.topSupportingLine_spec i).2 (right_mem_segment ℝ q p)
  apply affine_functionals_eq_smul_of_common_line (B.topSupportingLine i) (B.ambientTopFunctional i)
    (B.topSupportingLine_spec i).1 (B.ambientTopFunctional_surjective i) hne hq (B.ambientTopFunctional_left_vertex i)
  · change (B.topSupportingLine i).linear (p -ᵥ q) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hp, hq, sub_self]
  · change (B.ambientTopFunctional i).linear (p -ᵥ q) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, ambientTopFunctional_right_vertex, ambientTopFunctional_left_vertex, sub_self]

theorem ambientTopFunctional_horizontal (i : Fin B.faces.interface.count) :
    (B.ambientTopFunctional i).linear (G.frame.symm (1,0)) = -(B.faces.interface.piece i).linear 1 := by
  simpa [ambientTopFunctional] using B.faces.topLineFunctional_horizontal i
theorem ambientTopFunctional_pair_independent
    (i j : Fin B.faces.interface.count)
    (hne : (B.faces.interface.piece i).linear 1 ≠ (B.faces.interface.piece j).linear 1) :
    LinearIndependent ℝ
      (![(B.ambientTopFunctional i).linear, (B.ambientTopFunctional j).linear] : Fin 2 → Module.Dual ℝ Plane) := by
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · intro h
    change (B.ambientTopFunctional j).linear = 0 at h
    have hv := B.ambientTopFunctional_vertical j
    rw [h, LinearMap.zero_apply] at hv
    exact zero_ne_one hv
  · intro r he
    have hv := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (G.frame.symm (0, 1))) he
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.smul_apply,
      ambientTopFunctional_vertical, smul_eq_mul, mul_one] at hv
    have hh := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (G.frame.symm (1, 0))) he
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.smul_apply,
      ambientTopFunctional_horizontal, smul_eq_mul, hv, one_mul] at hh
    exact hne (neg_injective hh).symm

theorem ambientTopFunctional_isMonochromatic (N : TriangleMesh)
    (hN : ∀ l ∈ B.coreContactLines, N.IsMonochromatic l) (i : Fin B.faces.interface.count) :
    N.IsMonochromatic (B.ambientTopFunctional i) := by
  obtain ⟨r, _, he⟩ := B.ambientTopFunctional_eq_smul_topSupportingLine i
  rw [he]
  exact isMonochromatic_smul N (B.topSupportingLine i)
    (hN _ (by simp [coreContactLines, List.mem_ofFn])) r

theorem ambient_carrier_internal_top_eventually_iff
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ z in 𝓝 (B.chartTopVertex i.succ), z ∈ C.symm '' B.faces.carrier ↔
      if (B.faces.interface.piece i).linear 1 ≤ (B.faces.interface.piece j).linear 1 then
        B.ambientTopFunctional i z ≤ 0 ∨ B.ambientTopFunctional j z ≤ 0
      else B.ambientTopFunctional i z ≤ 0 ∧ B.ambientTopFunctional j z ≤ 0 := by
  have hc : ContinuousAt (fun z : Plane => collarParameterEquiv.symm (G.frame z))
      (B.chartTopVertex i.succ) :=
    (collarParameterEquiv.symm.continuous.comp G.frame.continuous).continuousAt
  have hv : collarParameterEquiv.symm (G.frame (B.chartTopVertex i.succ)) =
      B.faces.planarTopVertex i.succ := by simp [chartTopVertex, ObliqueBandFaces.planarTopVertex]
  have hlocal := hc.eventually (by
    simpa only [hv] using B.faces.planar_carrier_internal_top_eventually_iff i j hij)
  filter_upwards [hlocal] with z hz
  rw [mem_chart_image_iff_mem_linearGraphCoordinates_image C G.frame B.faces.carrier]
  exact hz

theorem exists_ambient_internal_top_sector_coordinates
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hne : (B.faces.interface.piece i).linear 1 ≠ (B.faces.interface.piece j).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.chartTopVertex i.succ ∧ c.coord 1 = B.ambientTopFunctional i ∧
        c.coord 2 = B.ambientTopFunctional j := by
  exact exists_affineBasis_coords_of_independent_functionals _ _ _
    (B.ambientTopFunctional_right_vertex i) (hij ▸ B.ambientTopFunctional_left_vertex j)
    (B.ambientTopFunctional_pair_independent i j hne)

theorem ambientTopFunctional_eq_of_adjacent_slope_eq
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (he : (B.faces.interface.piece i).linear 1 = (B.faces.interface.piece j).linear 1) :
    B.ambientTopFunctional i = B.ambientTopFunctional j := by
  unfold ambientTopFunctional
  rw [B.faces.topLineFunctional_eq_of_adjacent_slope_eq i j hij he]

theorem ambient_carrier_internal_top_halfspace_of_slope_eq
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (he : (B.faces.interface.piece i).linear 1 = (B.faces.interface.piece j).linear 1) :
    C.symm '' B.faces.carrier =ᶠ[𝓝 (B.chartTopVertex i.succ)]
      {z | B.ambientTopFunctional i z ≤ 0} := by
  have hfun := B.ambientTopFunctional_eq_of_adjacent_slope_eq i j hij he
  filter_upwards [B.ambient_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ C.symm '' B.faces.carrier ↔ B.ambientTopFunctional i z ≤ 0
  simpa only [he, le_refl, if_true, hfun, or_self] using hz

theorem exists_ambient_internal_top_convex_sector_coordinates
    (N : TriangleMesh) (hN : ∀ l ∈ B.coreContactLines, N.IsMonochromatic l)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece j).linear 1 < (B.faces.interface.piece i).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.chartTopVertex i.succ ∧
      c.coord 1 = -B.ambientTopFunctional i ∧ c.coord 2 = -B.ambientTopFunctional j ∧
      N.IsMonochromatic (c.coord 1) ∧ N.IsMonochromatic (c.coord 2) ∧
      C.symm '' B.faces.carrier =ᶠ[𝓝 (B.chartTopVertex i.succ)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have hind := (B.ambientTopFunctional_pair_independent i j hslope.ne').neg
  have hneg : LinearIndependent ℝ
      (![(-B.ambientTopFunctional i).linear, (-B.ambientTopFunctional j).linear] :
        Fin 2 → Module.Dual ℝ Plane) := by
    convert! hind using 1
    ext k
    fin_cases k <;> rfl
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_affineBasis_coords_of_independent_functionals
    (-B.ambientTopFunctional i) (-B.ambientTopFunctional j) (B.chartTopVertex i.succ)
    (by change -(B.ambientTopFunctional i (B.chartTopVertex i.succ)) = 0
        rw [B.ambientTopFunctional_right_vertex i, neg_zero])
    (by change -(B.ambientTopFunctional j (B.chartTopVertex i.succ)) = 0
        rw [hij, B.ambientTopFunctional_left_vertex j, neg_zero]) hneg
  have hmono (k : Fin B.faces.interface.count) :
      N.IsMonochromatic (-B.ambientTopFunctional k) := by
    simpa only [neg_one_smul] using isMonochromatic_smul N (B.ambientTopFunctional k)
      (B.ambientTopFunctional_isMonochromatic N hN k) (-1)
  refine ⟨c, hc0, hc1, hc2, hc1 ▸ hmono i, hc2 ▸ hmono j, ?_⟩
  filter_upwards [B.ambient_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ C.symm '' B.faces.carrier ↔ 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z
  rw [hc1, hc2]
  change z ∈ C.symm '' B.faces.carrier ↔ 0 ≤ -(B.ambientTopFunctional i z) ∧
    0 ≤ -(B.ambientTopFunctional j z)
  simpa only [not_le.mpr hslope, if_false, neg_nonneg] using hz

theorem exists_ambient_internal_top_reflex_sector_coordinates
    (N : TriangleMesh) (hN : ∀ l ∈ B.coreContactLines, N.IsMonochromatic l)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece i).linear 1 < (B.faces.interface.piece j).linear 1) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = B.chartTopVertex i.succ ∧
      c.coord 1 = B.ambientTopFunctional i ∧ c.coord 2 = B.ambientTopFunctional j ∧
      N.IsMonochromatic (c.coord 1) ∧ N.IsMonochromatic (c.coord 2) ∧
      C.symm '' B.faces.carrier =ᶠ[𝓝 (B.chartTopVertex i.succ)]
        {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  obtain ⟨c, hc0, hc1, hc2⟩ := B.exists_ambient_internal_top_sector_coordinates i j hij hslope.ne
  refine ⟨c, hc0, hc1, hc2, hc1 ▸ B.ambientTopFunctional_isMonochromatic N hN i,
    hc2 ▸ B.ambientTopFunctional_isMonochromatic N hN j, ?_⟩
  filter_upwards [B.ambient_carrier_internal_top_eventually_iff i j hij] with z hz
  apply propext
  change z ∈ C.symm '' B.faces.carrier ↔ c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0
  simpa only [hslope.le, if_true, hc1, hc2] using hz

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces
end PoincareConjecture.Topology.Surface
