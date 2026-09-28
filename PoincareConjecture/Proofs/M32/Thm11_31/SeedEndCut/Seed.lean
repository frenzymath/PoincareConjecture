import PoincareConjecture.Proofs.M32.Thm11_31.SeedEndCut.Prefix
import PoincareConjecture.Proofs.M32.Thm11_31.SeedEndCut.Topology
import PoincareConjecture.Proofs.M32.Neck.ScalarControl
import PoincareConjecture.Proofs.M32.Claim11_34.HornSeparation
import PoincareConjecture.Proofs.M32.Claim11_34.HornNonFilling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

theorem exists_horn_seed_endCut_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        (A : RepairedNeckCapTopologyTheory.{u})
        (H : SingularTimeAssumptions F T M) (Q : SingularLimitConclusion H)
        {epsilon : ℝ},
        0 < epsilon → epsilon ≤ epsilon₀ → epsilon ≤ A.epsilon₀ →
        ∀ (horn : StrongHorn Q.extension epsilon) (rho level : ℝ),
          ∃ N : TerminalStrongNeck Q.extension epsilon,
            N.center ∈ horn.carrier ∧
            level < (Q.extension.extended.connection T).scalarCurvature N.center ∧
            N.carrier ⊆ horn.carrier ∧ Nonempty (HornEndCut horn N rho) := by
  obtain ⟨epsilon₁, hp₁, _hs₁, hscalar⟩ := exists_strongNeck_scalarComparison.{u}
  obtain ⟨epsilon₂, hp₂, _hs₂, hseparate⟩ := exists_horn_boundary_sphere_transport.{u}
  obtain ⟨epsilon₃, hp₃, hs₃, hf₃, hnonfill⟩ := exists_horn_neck_nonfilling_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ epsilon₃), lt_min hp₁ (lt_min hp₂ hp₃),
    ((min_le_right _ _).trans (min_le_right _ _)).trans hs₃,
    ((min_le_right _ _).trans (min_le_right _ _)).trans hf₃, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ A H Q epsilon hepos he hA horn rho level
  classical
  have he₁ : epsilon ≤ epsilon₁ := he.trans (min_le_left _ _)
  have he₂ : epsilon ≤ epsilon₂ :=
    (he.trans (min_le_right _ _)).trans (min_le_left _ _)
  have he₃ : epsilon ≤ epsilon₃ :=
    (he.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hhalf : epsilon < 1 / 2 := (he₃.trans hs₃).trans_lt (by norm_num)
  obtain ⟨b, _hb0, _hb1, hcompact, hconnected, _hprefix, hboundary, hlow⟩ :=
    horn_exists_compact_connected_low_prefix Q horn rho
  let P := horn.parameterization '' (univ ×ˢ Icc 0 b)
  let R := (Q.extension.extended.connection T).scalarCurvature
  obtain ⟨p, _hp, hmax⟩ := hcompact.exists_isMaxOn hconnected.nonempty
    (Q.extension.extended.connection T).continuous_scalarCurvature.continuousOn
  obtain ⟨c, hc0, hc1, hhigh⟩ := horn_exists_tail_scalar_gt Q horn (max level (2 * R p))
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨s, hs⟩ := hsphere
  let q : UnitTwoSphere := ⟨s, hs⟩
  let t := (c + 1) / 2
  have hct : c < t := by dsimp only [t]; linarith
  have ht1 : t < 1 := by dsimp only [t]; linarith
  let x := horn.parameterization (q, t)
  have hx : x ∈ horn.carrier := by
    have h := (horn.coordinate (q, ⟨t, hc0.trans hct.le, ht1⟩)).property
    rwa [horn.coordinate_eq] at h
  have hxR : max level (2 * R p) < R x := hhigh q t hct ht1
  obtain ⟨N, hcenter⟩ := horn.every_point_neck x hx
  have hNcenter : N.center ∈ horn.carrier := by
    rw [hcenter]
    exact hx
  have hNhigh (y : (Q.extension.extended.slice T).carrier) (hy : y ∈ N.carrier) :
      R p < R y := by
    have hcomp := (hscalar N he₁ y hy).1
    rw [hcenter] at hcomp
    have htwice : 2 * R p < R x := (le_max_right _ _).trans_lt hxR
    change R x / 2 < R y at hcomp
    linarith
  have havoid : Disjoint N.carrier P :=
    disjoint_left.mpr (fun y hy hyP => (hNhigh y hy).not_ge (hmax hyP))
  let V := spatialNeck N hhalf
  have hinside : N.carrier ⊆ horn.carrier := by
    apply horn_subset_carrier_of_isPreconnected horn V.isConnected_carrier.isPreconnected
      ⟨N.center, N.central_sphere_subset N.center_on_central_sphere, hNcenter⟩
    exact disjoint_left.mpr (fun y hy hyb => disjoint_left.mp havoid hy (hboundary hyb))
  obtain ⟨_, _, _, _, _, hsep⟩ :=
    hseparate Q.extension hepos he₂ horn V rfl hNcenter
  have hr : 32 * Real.pi < V.epsilon⁻¹ := by
    have hbound : 64 * Real.pi ≤ epsilon⁻¹ := by
      simpa only [one_div, inv_inv] using inv_anti₀ hepos (he₃.trans hf₃)
    change 32 * Real.pi < epsilon⁻¹
    linarith [Real.pi_pos]
  have hcollar : N.coordinate_map '' (univ ×ˢ Icc (-(32 * Real.pi)) (32 * Real.pi)) ⊆
      horn.carrier := (V.closedCollar_subset_carrier hr).trans hinside
  have hfill := hnonfill Q.extension A hepos he₃ hA horn N hNcenter hcollar
  obtain ⟨cut, _hcutP⟩ := hornEndCut_exists_of_separating_neck_avoiding_prefix
    horn N hhalf rho hsep hconnected.isPreconnected hboundary hlow hinside havoid hfill
  refine ⟨N, hNcenter, ?_, hinside, ⟨cut⟩⟩
  rw [hcenter]
  exact (le_max_left _ _).trans_lt hxR

end PoincareConjecture.M32
