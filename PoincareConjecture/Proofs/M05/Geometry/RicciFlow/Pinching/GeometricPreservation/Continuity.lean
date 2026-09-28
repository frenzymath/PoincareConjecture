
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TransportedCarrier
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Isometry











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators
open Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

theorem contMDiffWithinAt_ricci_spacetime_fields
    (F : RicciFlow 3 M (Ico a b)) {O : Set M} {t : ℝ} {x : M}
    (ht : t ∈ Ico a b) (hx : x ∈ O)
    (X Y : (p : ℝ × M) → TangentSpace (𝓡 3) p.2)
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 3))
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
      (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin 3)) p.2 (X p))
      (Ico a b ×ˢ O) (t, x))
    (hY : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 3))
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
      (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin 3)) p.2 (Y p))
      (Ico a b ×ˢ O) (t, x)) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p => (F.connection p.1).ricci p.2 (X p) (Y p))
      (Ico a b ×ˢ O) (t, x) := by
  have hsub : Ico a b ×ˢ O ⊆ Ico a b ×ˢ (univ : Set M) :=
    prod_mono Subset.rfl (subset_univ O)
  have hR := ((contMDiffOn_ricciEndomorphism F) (t, x)
    ⟨ht, mem_univ _⟩).mono hsub
  have hG := (F.smooth (t, x) ⟨ht, mem_univ _⟩).mono hsub
  have h := hG.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (hR.clm_bundle_apply hX) hY
  apply (contMDiffWithinAt_totalSpace.mp h).2.congr_of_eventuallyEq_of_mem
    (hx := show (t, x) ∈ Ico a b ×ˢ O from ⟨ht, hx⟩)
  filter_upwards [self_mem_nhdsWithin] with p hp
  rw [metric_ricciEndomorphism_left, ricciBilin_apply F p.2 hp.1]
  rfl

end PoincareConjecture.RicciFlow.Frame
