import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.CapMotion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.Coordinates



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

open Poincare.Geometry.Euclidean
private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem exists_model_cap_stretch
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {d k : Real} (hd : 0 ≤ d) (hk : 0 < k)
    (P : Set E3) (hP : IsClosed P)
    (havoid : ∀ q : Hemisphere.Plane v, ‖q‖ ≤ 1 →
      ∀ z ∈ Icc (1 / 4 : Real) 2, ∀ t ∈ Icc (0 : Real) 1,
        (b + s * ((1 - t) * z + t * (d + k * z))) • v + (A q : E3) ∉ P) :
    ∃ J : Set E3, IsCompact J ∧ Disjoint J P ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ J, F y = y) ∧ (∀ y ∈ P, F y = y) ∧
        F '' (liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) =
          (liftPlaneDiffeomorph hv (b + s * d) (s * k) (mul_ne_zero hs hk.ne') A ''
            boundedCylinderNorthernCap v) ∪
          {y | (inner Real v y - b) / s ∈ Icc 0 d ∧
            (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1} := by
  let H := scaledCapCoordinates hv b s hs A
  obtain ⟨J, hJ, hJP, F, hfix, hfixP, hcap⟩ := exists_cap_affine_stretch_in_coordinates
    H (normalizedModelCap hv) (isCompact_normalizedModelCap hv)
    (sphere (0 : Hemisphere.Plane v) 1) (b := 1 / 4) (by norm_num) hd hk
    (fun _ hp => (normalizedModelCap_bounds hv hp).1)
    (fun q _ hz => mem_normalizedModelCap_belt hv q hz) P hP
    (by
      intro p hp hpz t ht
      rw [show H = scaledCapCoordinates hv b s hs A from rfl, scaledCapCoordinates_apply]
      exact havoid p.1 (normalizedModelCap_bounds hv hp).2.2 p.2
        ⟨hpz, (normalizedModelCap_bounds hv hp).2.1⟩ t ht)
  have hsource : H '' normalizedModelCap hv =
      liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v :=
    image_normalizedModelCap hv b s hs A
  have haff : H '' ((fun p : Hemisphere.Plane v × Real => (p.1, d + k * p.2)) ''
      normalizedModelCap hv) =
      liftPlaneDiffeomorph hv (b + s * d) (s * k) (mul_ne_zero hs hk.ne') A ''
        boundedCylinderNorthernCap v := by
    rw [← image_normalizedModelCap hv (b + s * d) (s * k) (mul_ne_zero hs hk.ne') A,
      ← image_comp]
    apply image_congr
    intro p _
    change scaledCapCoordinates hv b s hs A (p.1, d + k * p.2) = _
    rw [scaledCapCoordinates_apply, scaledCapCoordinates_apply]
    congr 2
    ring
  have hcyl : H '' (sphere (0 : Hemisphere.Plane v) 1 ×ˢ Icc 0 d) =
      {y | (inner Real v y - b) / s ∈ Icc 0 d ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1} := by
    have hheight (p : Hemisphere.Plane v × Real) : (inner Real v (H p) - b) / s = p.2 := by
      rw [show H = scaledCapCoordinates hv b s hs A from rfl, inner_scaledCapCoordinates]
      field_simp
      ring
    have hproj (p : Hemisphere.Plane v × Real) :
        (Hemisphere.Plane v).orthogonalProjectionOnto (H p) = A p.1 :=
      projection_scaledCapCoordinates hv b s hs A p
    ext y
    have hHs : Surjective (H : Hemisphere.Plane v × Real -> E3) := H.surjective
    obtain ⟨p, rfl⟩ := hHs y
    have hHi : Injective (H : Hemisphere.Plane v × Real -> E3) := H.injective
    have hAi : Injective (A : Hemisphere.Plane v -> Hemisphere.Plane v) := A.injective
    rw [hHi.mem_set_image]
    change (p.1 ∈ sphere 0 1 ∧ p.2 ∈ Icc 0 d) ↔ _
    simp only [mem_ofPred_eq, hheight, hproj, hAi.mem_set_image, and_comm]
  refine ⟨J, hJ, hJP, F, hfix, hfixP, ?_⟩
  rwa [hsource, haff, hcyl] at hcap

end Poincare.Manifold.Schoenflies.Reverse
