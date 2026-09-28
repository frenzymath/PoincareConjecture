import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.IntersectingRegions








noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem neck_below_calibrated_level_of_linear_low_point
    (Q : SingularLimitConclusion H)
    (N : EpsilonNeck (Q.extension.extended.metric T))
    (hepsilon : N.epsilon ≤ 1 / 200) (rho : ℝ)
    (hconstant : 1 ≤ H.constant)
    (hlow : ∃ x ∈ N.carrier,
      Q.terminal_scalar x ≤ 2 * H.constant * rho⁻¹ ^ 2) :
    ∀ y ∈ N.carrier,
      Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2 := by
  obtain ⟨x, hx, hlow⟩ := hlow
  intro y hy
  have hratio := N.scalar_lt_two_mul_of_mem_carrier
    (Q.extension.extended.connection T) hepsilon hy hx
  rw [← Q.terminal_scalar_eq] at hratio
  have hC : H.constant ≤ H.constant ^ 2 := by
    nlinarith [sq_nonneg (H.constant - 1)]
  have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg rho⁻¹)
  have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
      4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
    rw [inv_div, div_eq_mul_inv]
    ring
  rw [hid]
  nlinarith



theorem exists_tube_neck_at_linear_level (Q : SingularLimitConclusion H)
    {X : Set (Q.extension.extended.slice T).carrier}
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ X)
    (hlevel : Q.terminal_scalar x = 2 * H.constant * rho⁻¹ ^ 2) :
    ∃ i : ℤ, i ∈ tube.chain.shape.active ∧
      x ∈ (tube.chain.neck i).carrier ∧
      Disjoint (tube.chain.neck i).carrier
        {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      (∀ y ∈ (tube.chain.neck i).carrier,
        Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2) ∧
      SmoothSphereIsotopicIn tube.carrier
        (tube.chain.neck i).central_sphere tube.cylinder.middleSphere := by
  have hxtube := tube.contains_X hx
  rw [tube.carrier_eq_chain_union] at hxtube
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtube
  have hepsilon : (tube.chain.neck i.val).epsilon ≤ 1 / 200 :=
    (tube.chain.epsilon_eq i.val i.property).trans_le tube.epsilon_le_threshold
  exact ⟨i.val, i.property, hxi,
    Q.neck_disjoint_low_core_of_high_point (tube.chain.neck i.val)
      hepsilon rho hconstant ⟨x, hxi, hlevel.ge⟩,
    Q.neck_below_calibrated_level_of_linear_low_point (tube.chain.neck i.val)
      hepsilon rho hconstant ⟨x, hxi, hlevel.le⟩,
    tube.central_sphere_isotopy i.val i.property⟩



theorem cappedTube_neck_or_cap_at_linear_level (Q : SingularLimitConclusion H)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hcap : Y.cap.cap_constant ≤ 2 * H.constant)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ Y.carrier)
    (hlevel : Q.terminal_scalar x = 2 * H.constant * rho⁻¹ ^ 2) :
    (∃ i : ℤ, i ∈ Y.tube.chain.shape.active ∧
      x ∈ (Y.tube.chain.neck i).carrier ∧
      Disjoint (Y.tube.chain.neck i).carrier
        {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      (∀ y ∈ (Y.tube.chain.neck i).carrier,
        Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2) ∧
      SmoothSphereIsotopicIn Y.tube.carrier
        (Y.tube.chain.neck i).central_sphere Y.tube.cylinder.middleSphere) ∨
    (x ∈ Y.cap.carrier ∧
      Disjoint Y.cap.carrier {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      ∀ y ∈ Y.cap.carrier,
        Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2) := by
  rw [Y.carrier_eq_union] at hx
  rcases hx with hxcap | hxtube
  · exact Or.inr ⟨hxcap,
      Q.cap_disjoint_low_core_of_linear_high_point Y.cap rho hcap
        ⟨x, hxcap, hlevel.ge⟩,
      Q.cap_below_calibrated_level_of_linear_low_point Y.cap rho hcap
        ⟨x, hxcap, hlevel.le⟩⟩
  · let tube : EpsilonTubeCertificate (Q.extension.extended.metric T) Y.tube.carrier :=
      { Y.tube with contains_X := Subset.rfl }
    exact Or.inl (Q.exists_tube_neck_at_linear_level tube rho hconstant hxtube hlevel)

end PoincareConjecture.SingularLimitConclusion
