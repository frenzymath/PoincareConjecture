import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckConstructor









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem capAffineNeck_full_fields (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lt : epsilon < 1 / 2) (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (hscalar :
      0 < N.connection.scalarCurvature (N.coordinate_map (q, c)))
    (hclose : RoundCylinderClose epsilon 0 (fun z v w =>
      N.connection.scalarCurvature (N.coordinate_map (q, c)) *
        roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w)) :
    let E := capAffineNeck N hepsilon hepsilon_lt hlambda hdomain q hscalar hclose
    E.epsilon = epsilon ∧ E.connection = N.connection ∧
      E.carrier = N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹) ∧
      E.coordinate_map = N.coordinate_map ∘ neckAxialSpaceMap lambda c ∧
      E.coordinate_inverse = neckAxialInverse lambda c ∘ N.coordinate_inverse ∧
      E.central_sphere = N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  change (N.coordinate_map ∘ neckAxialSpaceMap lambda c) ''
    (univ ×ˢ ({0} : Set ℝ)) = N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ))
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    refine ⟨(z.1, c), ⟨mem_univ _, rfl⟩, ?_⟩
    simp only [Function.comp_apply, neckAxialSpaceMap, hz0, mul_zero, zero_add]
  · rintro ⟨z, hz, rfl⟩
    have hzc : z.2 = c := hz.2
    refine ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    simp only [Function.comp_apply, neckAxialSpaceMap, mul_zero, zero_add, ← hzc]




theorem cap_affine_left_sphere_subset_negative_closure (N E : EpsilonNeck g)
    {epsilon lambda c b : ℝ} (hepsilon : 0 < epsilon) (hlambda : 0 < lambda)
    (hb : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hright : c + lambda * epsilon⁻¹ = N.epsilon⁻¹)
    (hleft : b = c - lambda * epsilon⁻¹)
    (hcarrier : E.carrier = N.region b N.epsilon⁻¹)
    (hinverse : E.coordinate_inverse = neckAxialInverse lambda c ∘ N.coordinate_inverse) :
    N.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) ⊆
      closure (E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  let d := c - lambda * epsilon⁻¹ / 2
  have he : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hbd : b < d := by dsimp [d]; nlinarith
  have hd : d < N.epsilon⁻¹ := by dsimp [d]; nlinarith
  have himage : N.coordinate_map '' (univ ×ˢ Ioo b d) ⊆
      E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) := by
    rintro x ⟨z, hz, rfl⟩
    have hzold : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨hb.1.trans hz.2.1, hz.2.2.trans hd⟩
    have hcoord := N.coordinate_inverse_coordinate_map_of_axial_mem hzold
    refine ⟨?_, ?_⟩
    · rw [hcarrier]
      refine ⟨N.coordinate_map_mem_of_axial_mem hzold, ?_⟩
      rw [hcoord]
      exact ⟨hz.2.1, hzold.2⟩
    · rw [hinverse, Function.comp_apply, hcoord]
      change (z.2 - c) / lambda ∈ Ioo (-epsilon⁻¹) (-epsilon⁻¹ / 2)
      constructor
      · apply (lt_div_iff₀ hlambda).mpr
        nlinarith [hz.2.1]
      · apply (div_lt_iff₀ hlambda).mpr
        dsimp [d] at hz
        nlinarith [hz.2.2]
  rintro x ⟨z, hz, rfl⟩
  have hzb : z.2 = b := hz.2
  have hzold : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hzb.symm ▸ hb
  have hzcl : z ∈ closure (univ ×ˢ Ioo b d) := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hbd.ne]
    exact ⟨mem_univ _, by rw [hzb]; exact ⟨le_rfl, hbd.le⟩⟩
  have hcont := N.coordinate_map_smooth.continuousOn.continuousAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzold⟩)
  exact closure_mono himage (hcont.continuousWithinAt.mem_closure_image hzcl)

end PoincareConjecture.M47
