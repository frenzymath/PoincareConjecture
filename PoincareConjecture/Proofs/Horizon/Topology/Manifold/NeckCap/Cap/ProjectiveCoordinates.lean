import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Cap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]



theorem CapModelEquivalence.nonempty_projective_cover
    {p : RealProjectiveThree} {U : Set M}
    (model : CapModelEquivalence .puncturedProjective p U) (hU : IsOpen U) :
    Nonempty (StandardPuncturedProjectiveCover M p U) := by
  let : TopologicalSpace model.model := model.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.model := model.model_charted
  let : IsManifold (𝓡 3) ∞ model.model := model.model_manifold
  obtain ⟨S⟩ := model.standard_smooth
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) model.model M ∞ := {
    toFun := model.inverse
    invFun := model.forward
    source := univ
    target := U
    map_source' := fun y _ => model.inverse_mem y
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun y _ => model.right_inverse y
    right_inv' := fun x hx => model.left_inverse x hx
    open_source := isOpen_univ
    open_target := hU
    contMDiffOn_toFun := model.inverse_smooth
    contMDiffOn_invFun := model.forward_smooth }
  have hinj : Function.Injective model.inverse :=
    Function.LeftInverse.injective model.right_inverse
  refine ⟨{
    cover := model.inverse ∘ S.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · rw [image_comp, S.image_eq]
    apply Subset.antisymm
    · rintro _ ⟨y, _, rfl⟩
      exact model.inverse_mem y
    · intro x hx
      exact ⟨model.forward x, mem_univ _, model.left_inverse x hx⟩
  · intro x y hx hy
    exact hinj.eq_iff.trans (S.fibers x y hx hy)
  · intro x
    exact (S.local_diffeomorph x).comp (𝓡 3) M
      (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (mem_univ _))

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}


theorem CapCertificate.nonempty_projective_cover (C : CapCertificate g)
    (hkind : C.model_kind = .puncturedProjective) :
    Nonempty (StandardPuncturedProjectiveCover M C.puncture C.carrier) := by
  have model : CapModelEquivalence .puncturedProjective C.puncture C.carrier :=
    hkind ▸ C.model_equivalence
  exact model.nonempty_projective_cover C.carrier_open

end PoincareConjecture
