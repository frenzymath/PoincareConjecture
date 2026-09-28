import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Caps
import Mathlib.Analysis.Normed.Module.Connected



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem minimum_circle_eq_level_component
    {M : Type*} [TopologicalSpace M] [T2Space M] {h : M -> Real}
    (e : OpenPartialHomeomorph E2 M) {r c : Real} (hr : 0 < r)
    (hrs : closedBall (0 : E2) r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2)
    {p : M} (hp : p ∈ e '' sphere (0 : E2) r) :
    e '' sphere (0 : E2) r = connectedComponentIn (h ⁻¹' {c + r ^ 2}) p := by
  let C := e '' sphere (0 : E2) r
  let L := h ⁻¹' {c + r ^ 2}
  have hCs : sphere (0 : E2) r ⊆ e.source := sphere_subset_closedBall.trans hrs
  have hcompact : IsCompact C :=
    (isCompact_sphere 0 r).image_of_continuousOn (e.continuousOn.mono hCs)
  have hconn : IsPreconnected C :=
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) hr.le).isPreconnected.image
      e (e.continuousOn.mono hCs)
  have hClocal : C = e.target ∩ L := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.map_source (hCs hx), ?_⟩
      change h (e x) = c + r ^ 2
      rw [hform x (hCs hx), mem_sphere_zero_iff_norm.mp hx]
    · rintro ⟨hq, hh⟩
      refine ⟨e.symm q, ?_, e.right_inv hq⟩
      change h q = c + r ^ 2 at hh
      rw [← e.right_inv hq, hform _ (e.map_target hq)] at hh
      rw [mem_sphere_zero_iff_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (add_left_cancel hh)
  have hCL : C ⊆ L := hClocal ▸ inter_subset_right
  apply Subset.antisymm (hconn.subset_connectedComponentIn hp hCL)
  have hclopen : IsClopen ((Subtype.val : L -> M) ⁻¹' C) := by
    refine ⟨hcompact.isClosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : L -> M) ⁻¹' C = Subtype.val ⁻¹' e.target := by
      ext q
      simp only [mem_preimage, hClocal, mem_inter_iff, and_iff_left_iff_imp]
      exact fun _ => q.property
    rw [heq]
    exact e.open_target.preimage continuous_subtype_val
  rw [connectedComponentIn_eq_image (hCL hp)]
  rintro q ⟨x, hx, rfl⟩
  exact hclopen.connectedComponent_subset hp hx

end Poincare.Manifold.Schoenflies
