import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartTransitions

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_chart_surface_motion
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (B : OpenPartialHomeomorph X E)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hJB : J.space ⊆ B.target) {P₀ : Set E} (hP₀J : P₀ ⊆ J.space)
    {ε : ℝ} (H : PLCarrierMotion J.space P₀ ε)
    (S : Set X) (P : Set E)
    (hlocal : ∀ x ∈ J.space, B.symm x ∈ S ↔ x ∈ P) :
    ∃ F : X ≃ₜ X,
      (∀ x ∈ B.target, F (B.symm x) = B.symm (H.map 1 x)) ∧
      EqOn F id (B.symm '' J.space)ᶜ ∧ EqOn F id (B.symm '' P₀) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      ∀ x ∈ J.space, B.symm x ∈ F '' S ↔ x ∈ H.map 1 '' P := by
  obtain ⟨G, _, _, _, hGQ, hGout, hGprotected, _, _⟩ :=
    PLCarrierMotion.exists_chart_motion J hJ H B.symm hJB (hP₀J.trans hJB)
  have htrans := PLCarrierMotion.chart_transitions J hJ H B.symm hJB
    e he hB 1 (G 1) (hGQ 1) (hGout 1)
  have hcoord (x : E) (hx : x ∈ B.target) :
      G 1 (B.symm x) = B.symm (H.map 1 x) := by
    have h := hGQ 1 (B.map_target hx)
    change G 1 (B.symm x) = B.symm (H.map 1 (B (B.symm x))) at h
    rw [B.right_inv hx] at h
    exact h
  refine ⟨G 1, hcoord, hGout 1, hGprotected 1, htrans.1, htrans.2, ?_⟩
  intro x hx
  let z := (H.map 1).symm x
  have hz : z ∈ J.space := by
    apply (H.mem_superset_iff (Subset.rfl : J.space ⊆ J.space) 1 z).mp
    simpa only [z, Homeomorph.apply_symm_apply] using hx
  have hzx : H.map 1 z = x := (H.map 1).apply_symm_apply x
  have hGzx : G 1 (B.symm z) = B.symm x := by
    rw [hcoord z (hJB hz), hzx]
  have hwhole : B.symm x ∈ G 1 '' S ↔ B.symm z ∈ S := by
    constructor
    · rintro ⟨y, hy, hyeq⟩
      have hyz : y = B.symm z := (G 1).injective (hyeq.trans hGzx.symm)
      exact hyz ▸ hy
    · intro hzS
      exact ⟨B.symm z, hzS, hGzx⟩
  rw [hwhole, hlocal z hz]
  constructor
  · intro hzP
    exact ⟨z, hzP, hzx⟩
  · rintro ⟨y, hy, hyeq⟩
    have hyz : y = z := (H.map 1).injective (hyeq.trans hzx.symm)
    exact hyz ▸ hy

end PoincareConjecture.M76
