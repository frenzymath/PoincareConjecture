import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ModelComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_strongEvolvingNeck_of_exactCylinder
    (K : AncientKappaSolution 3 M) {t epsilon : ℝ} (ht : t ≤ 0)
    (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2)
    (x : M) (hR : 0 < (K.flow.connection t).scalarCurvature x)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (q : UnitTwoSphere) (hq : Φ (q, 0) = x)
    (hmodel : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (fun z v w => (K.flow.connection t).scalarCurvature x *
        roundCylinderPullback
          (K.flow.metric (t + u / (K.flow.connection t).scalarCurvature x))
          Φ z v w) = EvolvingRoundCylinderMetric u) :
    ∃ N : StrongEvolvingNeck K t epsilon,
      N.center = x ∧ N.terminal_neck.coordinate_map = Φ := by
  let R := (K.flow.connection t).scalarCurvature x
  let e := Φ.toHomeomorph.toOpenPartialHomeomorph.restrOpen
    (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) (isOpen_univ.prod isOpen_Ioo)
  have hsource : e.source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    change univ ∩ (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) = _
    exact univ_inter _
  have hcentral : e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ from
        ⟨neg_neg_of_pos hpos, hpos⟩)⟩
  have hscale : (R ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) = R := by
    rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num [R]
  have hterminal : (fun z v w => R *
      roundCylinderPullback (K.flow.metric t) Φ z v w) =
        EvolvingRoundCylinderMetric 0 := by
    simpa only [zero_div, add_zero] using hmodel 0 (by norm_num)
  let terminal : EpsilonNeck (K.flow.metric t) := {
    epsilon := epsilon
    epsilon_pos := hε
    epsilon_lt_half := hεhalf
    scale := R ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := x
    connection := K.flow.connection t
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := e
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := Φ.contMDiff.contMDiffOn
    coordinate_inverse := e.symm
    coordinate_inverse_mem := fun _ hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := Φ.symm.contMDiff.contMDiffOn
    central_sphere := e '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere :=
      ⟨(q, 0), ⟨mem_univ _, mem_singleton _⟩, hq⟩
    central_sphere_subset := hcentral
    metric_comparison := ⟨by
      change RoundCylinderClose epsilon 0 (fun z v w =>
        (R ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) *
          roundCylinderPullback (K.flow.metric t) Φ z v w)
      rw [hscale, hterminal]
      exact roundCylinderClose_model hε 0⟩ }
  refine ⟨{
    time_mem := ht
    center := x
    duration := R⁻¹
    duration_pos := inv_pos.mpr hR
    normalized_duration := inv_mul_cancel₀ hR.ne'
    terminal_neck := terminal
    terminal_center := rfl
    terminal_epsilon := rfl
    terminal_connection := rfl
    metric_comparison := ?_ }, rfl, rfl⟩
  change RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
    (fun u z v w => (K.flow.connection t).scalarCurvature x *
      roundCylinderPullback
        (K.flow.metric (t + u / (K.flow.connection t).scalarCurvature x)) Φ z v w)
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro u hu
    dsimp only
    rw [hmodel u hu]
    exact (roundCylinderFamilyClose_model hε (Ioc (-1 : ℝ) 0)).1 u hu
  · intro u hu z _
    dsimp only
    rw [hmodel u hu, roundCylinderJetErrorSquared_model]

end PoincareConjecture
