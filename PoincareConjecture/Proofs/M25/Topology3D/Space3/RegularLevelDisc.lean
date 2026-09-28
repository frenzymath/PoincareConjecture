import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelCircle
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc











set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem exists_regular_collar_component_disc (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x : collarHeightLevel ψ (u : E3) t) :
    ∃ B : BallNeighborhoodChart E2 E2,
      (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) '' B.boundary =
        ((↑) : collarHeightLevel ψ (u : E3) t → E3) '' connectedComponent x := by
  obtain ⟨e, hes, hed⟩ := exists_regular_collar_component_circle ψ hψ (u : E3) t hreg x
  let c : UnitCircle → E3 := fun q => ((e q).1 : E3)
  have hci : Injective c :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.injective)
  have hct (q : UnitCircle) : ⟪(u : E3), c q⟫_ℝ = t := by
    obtain ⟨p, hp, heq⟩ := (e q).1.2
    change ⟪(u : E3), ((e q).1 : E3)⟫_ℝ = t
    rw [← heq]
    exact hp
  let g : UnitCircle → E2 := fun q => (heightPlaneCoordinates u (c q)).1
  have hg : IsPlanarEmbedding g :=
    isPlanarEmbedding_height_projection u c hes hci hed t hct
  obtain ⟨D⟩ := hP.1 g hg
  refine ⟨D.ballNeighborhoodChart, ?_⟩
  change (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) ''
    (D.discChart '' Metric.sphere 0 1) = _
  rw [D.discChart_image_sphere, ← range_comp]
  have hrec : (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) ∘ g = c :=
    funext fun q => heightPlaneCoordinates_reconstruct u (c q) t (hct q)
  rw [hrec]
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(e q).1, (e q).2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨q, hq⟩ := e.surjective ⟨z, hz⟩
    exact ⟨q, congrArg (fun w : connectedComponent x => (w.1 : E3)) hq⟩

end PoincareConjecture.M25.Topology3D
