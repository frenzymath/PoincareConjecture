import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M47.SeedImageBalls










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C B : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale I U)
  (D : PartialDiffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞)
  (V : Set B.carrier) (hV : V ⊆ D.source) (hmaps : MapsTo D V U)



noncomputable def seedCylinderSource : SurgeryFlowCylinder F B origin scale I V := by
  have himage (s : ℝ) (hs : s ∈ I) :
      (e.forward s hs ∘ D) '' V ⊆ e.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D x, hmaps hx, rfl⟩
  refine {
    scale_pos := e.scale_pos
    interval_connected := e.interval_connected
    time_subset := e.time_subset
    forward := fun s hs => e.forward s hs ∘ D
    inverse := fun s hs => D.symm ∘ e.inverse s hs
    forward_smooth := fun s hs => (e.forward_smooth s hs).comp
      (D.contMDiffOn.mono hV) hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    slab_compatibility := fun a b hab hJ hS s hs t ht hs' ht' x hx =>
      e.slab_compatibility a b hab hJ hS s hs t ht hs' ht' (D x) (hmaps hx)
    retained_at_surgery := fun s hs hT _ hearlier =>
      (himage s hs).trans (e.retained_at_surgery s hs hT hearlier)
    pre_retained_at_surgery := fun s hs hT _ t ht ht' x hx =>
      e.pre_retained_at_surgery s hs hT t ht ht' (D x) (hmaps hx)
    surgery_compatibility := fun s hs hT _ t ht ht' x hx =>
      e.surgery_compatibility s hs hT t ht ht' (D x) (hmaps hx)
  }
  · intro s hs
    apply D.symm.contMDiffOn.comp ((e.inverse_smooth s hs).mono (himage s hs))
    rintro _ ⟨x, hx, rfl⟩
    change e.inverse s hs (e.forward s hs (D x)) ∈ D.target
    rw [e.left_inverse s hs (hmaps hx)]
    exact D.map_source (hV hx)
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs (hmaps hx)]
    exact D.left_inv (hV hx)
  · rintro s hs _ ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs (hmaps hx)]
    exact congrArg (fun z => e.forward s hs (D z)) (D.left_inv (hV hx))



theorem seedCylinderSource_forward (s : ℝ) (hs : s ∈ I) (x : B.carrier) :
    (seedCylinderSource e D V hV hmaps).forward s hs x = e.forward s hs (D x) := rfl


theorem seedCylinderSource_curvature {K : ℝ}
    (hK : ∀ s (hs : s ∈ I), ∀ x ∈ U,
      (F.connection (origin + s / scale)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    (s : ℝ) (hs : s ∈ I) (x : B.carrier) (hx : x ∈ V) :
    (F.connection (origin + s / scale)).curvatureTensorNorm
      ((seedCylinderSource e D V hV hmaps).forward s hs x) ≤ K :=
  hK s hs (D x) (hmaps hx)

end PoincareConjecture.Proofs.M47
