import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelPeriod
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PeriodicCurveSmooth

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_collar_component_circle
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x : collarHeightLevel ψ u t) :
    ∃ e : UnitCircle ≃ₜ connectedComponent x,
      ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ (fun q => ((e q).1 : E3)) ∧
      ∀ q, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (fun p => ((e p).1 : E3)) q) := by
  obtain ⟨T, hT, e₀, he₀, hv⟩ :=
    exists_regular_collar_component_period ψ hψ u t hreg x
  let H := periodUnitCircleHomeomorph T hT.ne'
  let e : UnitCircle ≃ₜ connectedComponent x := H.symm.trans e₀
  let c : UnitCircle → E3 := fun q => ((e q).1 : E3)
  have hlift : c ∘ periodCircleParam T =
      fun s : ℝ => ((e₀ (s : AddCircle T)).1 : E3) := by
    funext s
    change ((e₀ (H.symm (periodCircleParam T s))).1 : E3) = _
    rw [← periodUnitCircleHomeomorph_coe T hT.ne' s]
    change ((e₀ (H.symm (H (s : AddCircle T)))).1 : E3) = _
    rw [H.symm_apply_apply]
  have hs : ContDiff ℝ ∞ (c ∘ periodCircleParam T) := by
    rw [hlift]
    exact he₀
  have hnonzero : ∀ s, deriv (c ∘ periodCircleParam T) s ≠ 0 := by
    rw [hlift]
    exact hv
  exact ⟨e, contMDiff_of_smooth_period_lift T hT.ne' c hs,
    mfderiv_injective_of_nonzero_period_lift T hT.ne' c hs hnonzero⟩

end PoincareConjecture.M25.Topology3D
