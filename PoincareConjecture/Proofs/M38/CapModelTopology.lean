import PoincareConjecture.Proofs.M38.TubeExclusion









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]


noncomputable def capCarrierHomeomorph {kind : CapModelKind} {p : RealProjectiveThree}
    {U : Set M} (C : CapModelEquivalence kind p U) :
    letI := C.model_topology
    U ≃ₜ C.model := by
  letI := C.model_topology
  letI := C.model_charted
  letI := C.model_manifold
  exact {
    toFun := fun x => C.forward x.val
    invFun := fun y => ⟨C.inverse y, C.inverse_mem y⟩
    left_inv := fun x => Subtype.ext (C.left_inverse x.val x.property)
    right_inv := C.right_inverse
    continuous_toFun := C.forward_smooth.continuousOn.domRestrict
    continuous_invFun := (contMDiffOn_univ.mp C.inverse_smooth).continuous.subtype_mk _ }


theorem euclidean_cap_connected {p : RealProjectiveThree} {U : Set M}
    (C : CapModelEquivalence .euclidean p U) : IsConnected U := by
  let := C.model_topology
  let e : U ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin 3)) :=
    (capCarrierHomeomorph C).trans C.standard_model
  let : ConnectedSpace U := e.connectedSpace_iff.mpr inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance


theorem euclidean_cap_not_compact {p : RealProjectiveThree} {U : Set M}
    (C : CapModelEquivalence .euclidean p U) : ¬ IsCompact U := by
  intro hU
  let := C.model_topology
  let e : U ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    ((capCarrierHomeomorph C).trans C.standard_model).trans Homeomorph.ulift
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : CompactSpace (EuclideanSpace ℝ (Fin 3)) := e.compactSpace
  exact noncompact_univ (EuclideanSpace ℝ (Fin 3)) isCompact_univ


theorem no_euclidean_cap_containing_compact_component
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
    (x : M) (hx : IsCompact (connectedComponent x)) (C : CapCertificate g)
    (hkind : C.model_kind = .euclidean) : ¬ connectedComponent x ⊆ C.carrier := by
  intro hsub
  have hmodel : CapModelEquivalence .euclidean C.puncture C.carrier :=
    hkind ▸ C.model_equivalence
  have heq : C.carrier = connectedComponent x :=
    Set.Subset.antisymm
      ((euclidean_cap_connected hmodel).subset_connectedComponent
        (hsub mem_connectedComponent)) hsub
  exact euclidean_cap_not_compact hmodel (heq.symm ▸ hx)

end PoincareConjecture.M38
