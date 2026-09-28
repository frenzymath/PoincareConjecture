import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointAngles
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem affine_functional_eq_coordinate_combination_of_zero
    (c : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ) (hl : l (c 0) = 0) :
    l = l.linear (c 1 - c 0) • c.coord 1 + l.linear (c 2 - c 0) • c.coord 2 := by
  ext z
  have he := congrArg l.linear (affineBasis_direction_expansion c (z - c 0))
  have hcoord (i : Fin 3) : (c.coord i).linear (z - c 0) = c.coord i z - c.coord i (c 0) :=
    (c.coord i).linearMap_vsub z (c 0)
  rw [map_add, map_smul, map_smul, hcoord, hcoord] at he
  have hz := l.linearMap_vsub z (c 0)
  change l.linear (z - c 0) = l z - l (c 0) at hz
  rw [hl, sub_zero] at hz
  rw [hz] at he
  change l z = l.linear (c 1 - c 0) * c.coord 1 z + l.linear (c 2 - c 0) * c.coord 2 z
  simpa only [AffineBasis.coord_apply, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_zero, smul_eq_mul,
    mul_comm] using he

theorem coordinate_bend_sector_union (c : AffineBasis (Fin 3) ℝ Plane)
    (α : ℝ) (z : Plane) :
    ((0 ≤ c.coord 1 z ∧ c.coord 2 z ≤ 0) ∨
      (c.coord 1 z ≤ 0 ∧ c.coord 2 z + α * c.coord 1 z ≤ 0)) ↔
      if 0 ≤ α then c.coord 2 z ≤ 0 ∨ c.coord 2 z + α * c.coord 1 z ≤ 0
      else c.coord 2 z ≤ 0 ∧ c.coord 2 z + α * c.coord 1 z ≤ 0 := by
  by_cases ha : 0 ≤ α
  · rw [if_pos ha]
    constructor
    · exact fun h => h.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    · intro h
      by_cases hz : 0 ≤ c.coord 1 z
      · exact Or.inl ⟨hz, h.elim id (fun h => by nlinarith [mul_nonneg ha hz])⟩
      · have hn := le_of_not_ge hz
        exact Or.inr ⟨hn, h.elim (fun h => by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hn]) id⟩
  · rw [if_neg ha]
    have han := le_of_lt (lt_of_not_ge ha)
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact ⟨hy, by nlinarith [mul_nonpos_of_nonpos_of_nonneg han hx]⟩
      · exact ⟨by nlinarith [mul_nonneg_of_nonpos_of_nonpos han hx], hy⟩
    · intro h
      exact (le_total 0 (c.coord 1 z)).elim
        (fun hx => Or.inl ⟨hx, h.1⟩) (fun hx => Or.inr ⟨hx, h.2⟩)

theorem coordinate_linear_ray (c : AffineBasis (Fin 3) ℝ Plane)
    (i j : Fin 3) : (c.coord i).linear (c j - c 0) =
      (if i = j then 1 else 0) - (if i = 0 then 1 else 0) := by
  have h := (c.coord i).linearMap_vsub (c j) (c 0)
  simpa only [vsub_eq_sub, AffineBasis.coord_apply] using h

theorem coordinate_bend_normals_independent
    (c : AffineBasis (Fin 3) ℝ Plane) {α σ : ℝ} (hα : α ≠ 0) (hσ : σ ≠ 0) :
    LinearIndependent ℝ (![ (σ • c.coord 2).linear,
      (σ • (c.coord 2 + α • c.coord 1)).linear] : Fin 2 → Module.Dual ℝ Plane) := by
  have h11 : (c.coord 1).linear (c 1 - c 0) = 1 := by
    rw [coordinate_linear_ray]; norm_num
  have h12 : (c.coord 1).linear (c 2 - c 0) = 0 := by
    rw [coordinate_linear_ray]; norm_num [show (1 : Fin 3) ≠ 2 by decide]
  have h21 : (c.coord 2).linear (c 1 - c 0) = 0 := by
    rw [coordinate_linear_ray]
    norm_num [show (2 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 0 by decide]
  have h22 : (c.coord 2).linear (c 2 - c 0) = 1 := by
    rw [coordinate_linear_ray]; norm_num [show (2 : Fin 3) ≠ 0 by decide]
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have he := congrArg (fun l : Plane →ₗ[ℝ] ℝ => l (c 2 - c 0)) h
    change σ * ((c.coord 2).linear (c 2 - c 0) + α * (c.coord 1).linear (c 2 - c 0)) = 0 at he
    simp only [h12, h22, mul_zero, add_zero, mul_one] at he
    exact hσ he
  · intro r h
    have he2 := congrArg (fun l : Plane →ₗ[ℝ] ℝ => l (c 2 - c 0)) h
    change r * (σ * ((c.coord 2).linear (c 2 - c 0) + α * (c.coord 1).linear (c 2 - c 0))) =
      σ * (c.coord 2).linear (c 2 - c 0) at he2
    simp only [h12, h22, mul_zero, add_zero, mul_one] at he2
    have hr : r = 1 := mul_right_cancel₀ hσ (he2.trans (one_mul σ).symm)
    have he1 := congrArg (fun l : Plane →ₗ[ℝ] ℝ => l (c 1 - c 0)) h
    change r * (σ * ((c.coord 2).linear (c 1 - c 0) + α * (c.coord 1).linear (c 1 - c 0))) =
      σ * (c.coord 2).linear (c 1 - c 0) at he1
    simp only [hr, h11, h21, mul_one, zero_add, one_mul, mul_zero] at he1
    exact hα ((mul_eq_zero.mp he1).resolve_left hσ)

theorem exists_coordinate_bend_basis
    (c : AffineBasis (Fin 3) ℝ Plane) {α σ : ℝ} (hα : α ≠ 0) (hσ : σ ≠ 0) :
    ∃ d : AffineBasis (Fin 3) ℝ Plane, d 0 = c 0 ∧
      d.coord 1 = σ • c.coord 2 ∧ d.coord 2 = σ • (c.coord 2 + α • c.coord 1) := by
  apply exists_affineBasis_coords_of_independent_functionals _ _ (c 0)
  · change σ * c.coord 2 (c 0) = 0
    simp
  · change σ * (c.coord 2 (c 0) + α * c.coord 1 (c 0)) = 0
    simp
  · exact coordinate_bend_normals_independent c hα hσ

namespace FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : Plane} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

theorem adjacent_top_normal_cut_pos
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    0 < ((B j).ambientEndpointTop false).linear (K.direction i.succ) := by
  have hp := (B j).first_top_cut_determinant_pos
  change 0 < ((B j).ambientTopFunctional (B j).faces.firstCell).linear (K.direction i.succ)
  rw [(B j).ambientTopFunctional_linear, hij]
  exact hp

theorem exists_adjacent_top_coordinates
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∃ (c : AffineBasis (Fin 3) ℝ Plane) (α β : ℝ), 0 < β ∧
      c 0 = C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ ∧
      c.coord 1 = -(B i).ambientEndpointCut true ∧
      c.coord 2 = (B i).ambientEndpointTop true ∧
      (B j).ambientEndpointTop false = β • (c.coord 2 + α • c.coord 1) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := (B i).exists_ambient_last_complementary_coordinates (S.cut_lt i).le
  have hc0' : c 0 = C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using hc0
  obtain ⟨u, v, _, hv, _, hd⟩ := (B i).last_complementary_positive_rays c hc1 hc2
  have hd' : K.direction i.succ = v • (c 2 - c 0) := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using hd
  let l := (B j).ambientEndpointTop false
  let β := l.linear (c 2 - c 0)
  let γ := l.linear (c 1 - c 0)
  have hβ : 0 < β := by
    have hp := K.adjacent_top_normal_cut_pos B i j hij
    rw [hd', map_smul] at hp
    exact (mul_pos_iff_of_pos_left hv).mp hp
  have hl : l (c 0) = 0 := by
    rw [hc0', hij]
    have hz := ((B j).ambient_first_endpoint_functionals_vanish (S.cut_lt j).le).2
    simpa only [l, Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using hz
  refine ⟨c, γ / β, β, hβ, hc0', hc1, hc2, ?_⟩
  have he := affine_functional_eq_coordinate_combination_of_zero c l hl
  change l = β • (c.coord 2 + (γ / β) • c.coord 1)
  rw [he]
  ext z
  change γ * c.coord 1 z + β * c.coord 2 z =
    β * (c.coord 2 z + (γ / β) * c.coord 1 z)
  field_simp
  ring

theorem adjacent_top_carrier_coordinate_bend
    (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (c : AffineBasis (Fin 3) ℝ Plane) (α β : ℝ) (hβ : 0 < β)
    (hc0 : c 0 = C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ)
    (hc1 : c.coord 1 = -(B i).ambientEndpointCut true)
    (hc2 : c.coord 2 = (B i).ambientEndpointTop true)
    (he : (B j).ambientEndpointTop false = β • (c.coord 2 + α • c.coord 1)) :
    C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier) =ᶠ[𝓝 (c 0)]
      {z | if 0 ≤ α then c.coord 2 z ≤ 0 ∨ c.coord 2 z + α * c.coord 1 z ≤ 0
        else c.coord 2 z ≤ 0 ∧ c.coord 2 z + α * c.coord 1 z ≤ 0} := by
  have hlocal := K.adjacent_top_carrier_eventually_iff_common_cut B i j hij
  rw [← hc0] at hlocal
  filter_upwards [hlocal] with z hz
  apply propext
  change z ∈ C.symm '' _ ↔ _
  rw [hz, ← hc2, he]
  have hn : (B i).ambientEndpointCut true z = -c.coord 1 z := by
    rw [hc1]
    simp
  rw [hn]
  change ((-c.coord 1 z ≤ 0 ∧ c.coord 2 z ≤ 0) ∨
    (0 ≤ -c.coord 1 z ∧ β * (c.coord 2 z + α * c.coord 1 z) ≤ 0)) ↔ _
  have hm (v : ℝ) : β * v ≤ 0 ↔ v ≤ 0 := by
    constructor
    · intro h
      by_contra hn
      exact (mul_pos hβ (lt_of_not_ge hn)).not_ge h
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos hβ.le h
  simp only [hm, neg_nonpos, neg_nonneg]
  exact coordinate_bend_sector_union c α z

theorem adjacent_top_coordinate_ray_signs
    (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (c : AffineBasis (Fin 3) ℝ Plane) (α β : ℝ) (hβ : 0 < β)
    (hc1 : c.coord 1 = -(B i).ambientEndpointCut true)
    (hc2 : c.coord 2 = (B i).ambientEndpointTop true)
    (he : (B j).ambientEndpointTop false = β • (c.coord 2 + α • c.coord 1)) :
    let v := (B i).chartTopVertex (B i).faces.lastCell.castSucc -
      (B i).chartTopVertex (B i).faces.lastCell.succ
    let w := (B j).chartTopVertex (B j).faces.firstCell.succ - (B j).chartTopVertex 0
    (0 < (c.coord 1).linear v ∧ (c.coord 2).linear v = 0) ∧
      ((c.coord 1).linear w < 0 ∧ (c.coord 2 + α • c.coord 1).linear w = 0) ∧
      ((c.coord 1).linear (K.direction i.succ) = 0 ∧
        0 < (c.coord 2).linear (K.direction i.succ)) := by
  let v := (B i).chartTopVertex (B i).faces.lastCell.castSucc -
    (B i).chartTopVertex (B i).faces.lastCell.succ
  let w := (B j).chartTopVertex (B j).faces.firstCell.succ - (B j).chartTopVertex 0
  have h11 : (c.coord 1).linear (c 1 - c 0) = 1 := by
    rw [coordinate_linear_ray]; norm_num [Fin.ext_iff]
  have h12 : (c.coord 1).linear (c 2 - c 0) = 0 := by
    rw [coordinate_linear_ray]; norm_num [Fin.ext_iff]
  have h21 : (c.coord 2).linear (c 1 - c 0) = 0 := by
    rw [coordinate_linear_ray]; norm_num [Fin.ext_iff]
  have h22 : (c.coord 2).linear (c 2 - c 0) = 1 := by
    rw [coordinate_linear_ray]; norm_num [Fin.ext_iff]
  obtain ⟨u, s, hu, hs, hv, hd⟩ := (B i).last_complementary_positive_rays c hc1 hc2
  change v = u • (c 1 - c 0) at hv
  have hd' : K.direction i.succ = s • (c 2 - c 0) := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using hd
  obtain ⟨d, _, hd1, hd2⟩ := (B j).exists_ambient_first_complementary_coordinates (S.cut_lt j).le
  obtain ⟨t, _, ht, _, hw, _⟩ := (B j).first_complementary_positive_rays d hd1 hd2
  change w = t • (d 1 - d 0) at hw
  have hw1 : 0 < (-(B j).ambientEndpointCut false).linear w := by
    rw [← hd1, hw, map_smul, coordinate_linear_ray]
    simpa only [ite_true, show (1 : Fin 3) ≠ 0 by decide, ite_false,
      sub_zero, smul_eq_mul, mul_one] using ht
  have hw2 : ((B j).ambientEndpointTop false).linear w = 0 := by
    rw [← hd2, hw, map_smul, coordinate_linear_ray]
    norm_num [Fin.ext_iff]
  obtain ⟨k, hk, hop⟩ := K.adjacent_cut_functionals_opposite B i j hij
  have hop' : (B j).ambientEndpointCut false = k • c.coord 1 := by
    ext z
    rw [hc1]
    change (B j).ambientEndpointCut false z = k * (-(B i).ambientEndpointCut true z)
    rw [hop z]
    ring
  have hkw : 0 < -(k * (c.coord 1).linear w) := by
    rw [hop'] at hw1
    exact hw1
  have hn : (c.coord 1).linear w < 0 := by
    by_contra h
    have hp := mul_nonneg hk.le (le_of_not_gt h)
    linarith
  have hz : (c.coord 2 + α • c.coord 1).linear w = 0 := by
    rw [he] at hw2
    exact (mul_eq_zero.mp hw2).resolve_left hβ.ne'
  refine ⟨⟨?_, ?_⟩, ⟨hn, hz⟩, ?_, ?_⟩
  · change 0 < (c.coord 1).linear v
    rw [hv, map_smul, h11]
    simpa only [smul_eq_mul, mul_one] using hu
  · change (c.coord 2).linear v = 0
    rw [hv, map_smul, h21, smul_zero]
  · rw [hd', map_smul, h12, smul_zero]
  · rw [hd', map_smul, h22]
    simpa only [smul_eq_mul, mul_one] using hs

end FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

end PoincareConjecture.Topology.Surface
