import PoincareConjecture.Proofs.M34.Standard.CapImageTopology
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem nonempty_image_recutModelEquivalence
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {b : ℝ} (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    (hsource : N.recutCarrier b ⊆ e.source) :
    Nonempty (CapModelEquivalence N.model_kind N.puncture (e '' N.recutCarrier b)) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞ := {
    toFun := e
    invFun := e.symm
    source := N.recutCarrier b
    target := e '' N.recutCarrier b
    open_source := N.recutCarrier_isOpen hb hb'
    open_target := e.isOpen_image_of_subset_source (N.recutCarrier_isOpen hb hb') hsource
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [e.left_inv (hsource hx)] using hx
    left_inv' := fun x hx => e.left_inv (hsource hx)
    right_inv' := by
      rintro _ ⟨x, hx, rfl⟩
      exact e.right_inv (e.map_source (hsource hx))
    contMDiffOn_toFun := hf.mono hsource
    contMDiffOn_invFun := hi.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact e.map_source (hsource hx))
  }
  obtain ⟨model⟩ := N.nonempty_recutModelEquivalence hb hb'
  exact ⟨CapModelEquivalence.transport d model⟩

end PoincareConjecture.CapCertificate
