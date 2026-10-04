import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.NeckRegions

/-!
# Guarded ambient extensions of neck axial maps

The actual neck coordinate maps extend a real axial map by identity
outside the neck. Every coordinate identity and smoothness statement
below is guarded by membership in the valid neck strip. This is the
ambient gluing step of Morgan--Tian Proposition 9.79, pp. 232-234;
see the M28 cap-topology ambient-gluing derivation.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- Extend an axial map through the actual neck coordinates, using the
identity elsewhere. No meaning is assigned to off-strip coordinates. -/
noncomputable def axialMap (N : EpsilonNeck g) (β : ℝ → ℝ) (x : M) : M := by
  classical
  exact if x ∈ N.carrier then
    N.coordinate_map ((N.coordinate_inverse x).1, β (N.coordinate_inverse x).2) else x

/-- The guarded map has its displayed coordinate formula on the neck. -/
theorem axialMap_of_mem (N : EpsilonNeck g) (β : ℝ → ℝ) {x : M}
    (hx : x ∈ N.carrier) :
    N.axialMap β x = N.coordinate_map
      ((N.coordinate_inverse x).1, β (N.coordinate_inverse x).2) := by
  simp only [axialMap, if_pos hx]

/-- The guarded map is identity outside the neck. -/
theorem axialMap_of_not_mem (N : EpsilonNeck g) (β : ℝ → ℝ) {x : M}
    (hx : x ∉ N.carrier) : N.axialMap β x = x := by
  simp only [axialMap, if_neg hx]

/-- A fixed axial height fixes the actual ambient neck point. -/
theorem axialMap_eq_self_of_fixed_height (N : EpsilonNeck g) (β : ℝ → ℝ) {x : M}
    (hx : x ∈ N.carrier) (hfix : β (N.coordinate_inverse x).2 = (N.coordinate_inverse x).2) :
    N.axialMap β x = x := by
  rw [N.axialMap_of_mem β hx, hfix]
  exact N.coordinate_map_coordinate_inverse hx

/-- Valid transformed heights give actual membership in the indicated
neck region (Proposition 9.79, pp. 232-234). -/
theorem axialMap_mem_region (N : EpsilonNeck g) (β : ℝ → ℝ) {x : M}
    (hx : x ∈ N.carrier) {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹)
    (hβx : β (N.coordinate_inverse x).2 ∈ Ioo a b) :
    N.axialMap β x ∈ N.region a b := by
  have ht : β (N.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨ha.trans_lt hβx.1, hβx.2.trans_le hb⟩
  rw [N.axialMap_of_mem β hx]
  refine ⟨N.coordinate_map_mem_of_axial _ ht, ?_⟩
  rw [N.coordinate_inverse_coordinate_map_of_axial
    ((N.coordinate_inverse x).1, β (N.coordinate_inverse x).2) ht]
  exact hβx

/-- Inverse axial values give an actual ambient inverse identity as
long as the intermediate coordinate remains in the neck strip. -/
theorem axialMap_comp_eq (N : EpsilonNeck g) (β γ : ℝ → ℝ) {x : M}
    (hx : x ∈ N.carrier)
    (hβx : β (N.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hinv : γ (β (N.coordinate_inverse x).2) = (N.coordinate_inverse x).2) :
    N.axialMap γ (N.axialMap β x) = x := by
  rw [N.axialMap_of_mem β hx,
    N.axialMap_of_mem γ (N.coordinate_map_mem_of_axial _ hβx),
    N.coordinate_inverse_coordinate_map_of_axial _ hβx]
  change N.coordinate_map ((N.coordinate_inverse x).1,
    γ (β (N.coordinate_inverse x).2)) = x
  rw [hinv]
  exact N.coordinate_map_coordinate_inverse hx

/-- A smooth axial map gives actual ambient smoothness at every valid
neck point whose image height stays in the coordinate strip. -/
theorem contMDiffAt_axialMap (N : EpsilonNeck g) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) {x : M} (hx : x ∈ N.carrier)
    (hβx : β (N.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.axialMap β) x := by
  let ψ := fun z : UnitTwoSphere × ℝ => (z.1, β z.2)
  have hψ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ ψ :=
    contMDiff_fst.prodMk (hβ.contMDiff.comp contMDiff_snd)
  have hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      (ψ (N.coordinate_inverse x)) := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hβx⟩)
  have hi := N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hx)
  apply (hc.comp x (hψ.contMDiffAt.comp x hi)).congr_of_eventuallyEq
  filter_upwards [N.carrier_open.mem_nhds hx] with y hy
  exact N.axialMap_of_mem β hy

end PoincareMT.EpsilonNeck
