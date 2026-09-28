import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Caps







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem exists_gap_around_protected_height
    (L : List (SphereSurgeryCoreCap v g B)) {c : Real} (hc : c ∈ B) :
    ∃ ε : Real, 0 < ε ∧
      (∀ D ∈ L, ∀ x ∈ closedBall (0 : E2) 1,
        ε < |inner Real v (D.parametrization x) - c|) ∧
      ∀ D ∈ L, ε < |D.center - c| := by
  classical
  let K : Set Real := ⋃ D ∈ L,
    (fun x : E2 => inner Real v (D.parametrization x)) '' closedBall 0 1
  have hfinite : {D : SphereSurgeryCoreCap v g B | D ∈ L}.Finite := by
    simpa only [List.coe_toFinset] using L.toFinset.finite_toSet
  have hK : IsCompact K := hfinite.isCompact_biUnion (fun D _ =>
    (isCompact_closedBall 0 1).image
      ((innerSL Real v).continuous.comp D.parametrization_smooth.continuous))
  have hcK : c ∈ Kᶜ := by
    intro hmem
    obtain ⟨D, _, x, hx, hxc⟩ := mem_iUnion₂.mp hmem
    change inner Real v (D.parametrization x) = c at hxc
    exact D.avoids_protected x hx (hxc.symm ▸ hc)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds hcK)
  have hsep (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
      (x : E2) (hx : x ∈ closedBall 0 1) :
      δ / 2 < |inner Real v (D.parametrization x) - c| := by
    by_contra! hnot
    apply hδsub (show inner Real v (D.parametrization x) ∈ ball c δ by
      rw [mem_ball, Real.dist_eq]
      linarith)
    exact mem_iUnion_of_mem D (mem_iUnion_of_mem hD (mem_image_of_mem _ hx))
  refine ⟨δ / 2, half_pos hδ, hsep, ?_⟩
  intro D hD
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
  have h := hsep D hD x (sphere_subset_closedBall hx)
  rwa [D.boundary_height x hx] at h

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
