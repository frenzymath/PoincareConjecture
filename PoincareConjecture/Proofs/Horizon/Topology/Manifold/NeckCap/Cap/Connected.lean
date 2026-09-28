import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Cap
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere










set_option autoImplicit false

open scoped Manifold ContDiff
open Set

universe u

namespace PoincareConjecture

theorem connectedSpace_puncturedRealProjectiveThree (p : RealProjectiveThree) :
    ConnectedSpace (PuncturedRealProjectiveThree p) := by
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective p
  obtain ⟨e⟩ := Poincare.Topology.sphereComplementTwoPointsHomeomorphPuncturedEuclidean
    (n := 2) v
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let : ConnectedSpace ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    Subtype.connectedSpace (isConnected_compl_singleton_of_one_lt_rank hrank 0)
  let : ConnectedSpace ({v, -v}ᶜ : Set UnitThreeSphere) :=
    e.symm.surjective.connectedSpace e.symm.continuous
  let q : ({v, -v}ᶜ : Set UnitThreeSphere) →
      PuncturedRealProjectiveThree (Quotient.mk realProjectiveThreeSetoid v) :=
    fun x => ⟨Quotient.mk' x.val, by
      intro h
      have hx : x.val ≠ v ∧ x.val ≠ -v := by
        simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
          using x.property
      rcases Quotient.exact h with h | h
      · exact hx.1 h
      · exact hx.2 h⟩
  have hq : Continuous q :=
    (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := Quotient.mk_surjective y.val
    have hmem : x ∈ ({v, -v}ᶜ : Set UnitThreeSphere) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h
        subst x
        exact y.property hx.symm
      · intro h
        apply y.property
        rw [← hx]
        exact Quotient.sound (Or.inr h)
    exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩
  exact hsurj.connectedSpace hq

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem CapModelEquivalence.isConnected_carrier {kind : CapModelKind}
    {p : RealProjectiveThree} {carrier : Set M}
    (model : CapModelEquivalence kind p carrier) : IsConnected carrier := by
  let : TopologicalSpace model.model := model.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.model := model.model_charted
  let : IsManifold (𝓡 3) ∞ model.model := model.model_manifold
  have : ConnectedSpace model.model := by
    cases kind with
    | euclidean =>
      exact model.standard_model.symm.surjective.connectedSpace
        model.standard_model.symm.continuous
    | puncturedProjective =>
      let := connectedSpace_puncturedRealProjectiveThree p
      let : ConnectedSpace (ULift.{u} (PuncturedRealProjectiveThree p)) :=
        Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
      exact model.standard_model.symm.surjective.connectedSpace
        model.standard_model.symm.continuous
  have himage : model.inverse '' univ = carrier := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact model.inverse_mem y
    · intro hx
      exact ⟨model.forward x, mem_univ _, model.left_inverse x hx⟩
  rw [← himage]
  exact isConnected_univ.image _ model.inverse_smooth.continuousOn

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

omit [T2Space M] in
theorem CapCertificate.isConnected_carrier {g : RiemannianMetric 3 M}
    (cap : CapCertificate g) : IsConnected cap.carrier :=
  cap.model_equivalence.isConnected_carrier

end PoincareConjecture
