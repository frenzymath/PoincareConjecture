import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Cap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]


theorem CapModelEquivalence.exists_euclidean_coordinates
    {p : RealProjectiveThree} {U : Set M}
    (model : CapModelEquivalence .euclidean p U) (hU : IsOpen U) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      e.source = U ∧ e.target = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let : TopologicalSpace model.model := model.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.model := model.model_charted
  let : IsManifold (𝓡 3) ∞ model.model := model.model_manifold
  obtain ⟨d⟩ := model.standard_smooth
  let f : M → EuclideanSpace ℝ (Fin 3) := d ∘ model.forward
  let inv : EuclideanSpace ℝ (Fin 3) → M := model.inverse ∘ d.symm
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    d.contMDiff.comp_contMDiffOn model.forward_smooth
  have hinv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv univ :=
    model.inverse_smooth.comp d.symm.contMDiff.contMDiffOn (fun _ _ => mem_univ _)
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) := {
    toFun := f
    invFun := inv
    source := U
    target := univ
    map_source' := fun _ _ => mem_univ _
    map_target' := fun y _ => model.inverse_mem (d.symm y)
    left_inv' := by
      intro x hx
      change model.inverse (d.symm (d (model.forward x))) = x
      rw [d.symm_apply_apply]
      exact model.left_inverse x hx
    right_inv' := by
      intro y _
      change d (model.forward (model.inverse (d.symm y))) = y
      rw [model.right_inverse, d.apply_symm_apply]
    open_source := hU
    open_target := isOpen_univ
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hinv.continuousOn }
  exact ⟨e, rfl, rfl, hf, hinv⟩

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}


theorem CapCertificate.exists_euclidean_coordinates (C : CapCertificate g)
    (hkind : C.model_kind = .euclidean) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      e.source = C.carrier ∧ e.target = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  have model : CapModelEquivalence .euclidean C.puncture C.carrier :=
    hkind ▸ C.model_equivalence
  exact model.exists_euclidean_coordinates C.carrier_open

end PoincareConjecture
