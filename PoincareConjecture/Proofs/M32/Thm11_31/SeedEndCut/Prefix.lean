import PoincareConjecture.Proofs.M32.Thm11_31.Levels
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32




theorem horn_exists_compact_connected_low_prefix
    {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    {H : SingularTimeAssumptions F T M} (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension epsilon) (rho : ℝ) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      let P := horn.parameterization '' (univ ×ˢ Icc 0 b)
      IsCompact P ∧ IsConnected P ∧ P ⊆ horn.carrier ∧
        horn.boundary_sphere ⊆ P ∧
        horn.carrier ∩ {x | (Q.extension.extended.connection T).scalarCurvature x ≤
          rho⁻¹ ^ 2} ⊆ P := by
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  obtain ⟨b, hb0, hb1, hhigh⟩ := horn_exists_tail_scalar_gt Q horn (rho⁻¹ ^ 2)
  have hcontinuous : ContinuousOn horn.parameterization (univ ×ˢ Icc 0 b) := by
    apply horn.parameterization_smooth.continuousOn.mono
    intro z hz
    exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le hz.2.1,
      hz.2.2.trans_lt hb1⟩
  refine ⟨b, hb0, hb1,
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn hcontinuous,
    (isConnected_univ.prod (isConnected_Icc hb0)).image _ hcontinuous, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨s, t⟩, ⟨_, ht0, htb⟩, rfl⟩
    have hx := (horn.coordinate (s, ⟨t, ht0, htb.trans_lt hb1⟩)).property
    rwa [horn.coordinate_eq] at hx
  · rw [horn.boundary_sphere_eq]
    apply image_mono
    rintro ⟨s, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨mem_univ _, le_rfl, hb0⟩
  · intro x hx
    let z := horn.coordinate.symm ⟨x, hx.1⟩
    have hz : horn.parameterization (z.1, (z.2 : ℝ)) = x := by
      rw [← horn.coordinate_eq]
      exact congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨x, hx.1⟩)
    have hzb : (z.2 : ℝ) ≤ b := by
      by_contra hnot
      have hh := hhigh z.1 z.2 (lt_of_not_ge hnot) z.2.property.2
      rw [hz] at hh
      exact hh.not_ge hx.2
    exact ⟨(z.1, z.2), ⟨mem_univ _, z.2.property.1, hzb⟩, hz⟩

end PoincareConjecture.M32
