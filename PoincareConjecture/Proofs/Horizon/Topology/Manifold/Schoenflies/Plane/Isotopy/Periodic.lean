import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicCircle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

theorem exists_ambient_isotopy_of_periodic_family
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) {T a b : ℝ}
    (hT : 0 < T) (hab : a ≤ b) (γ : ℝ → ℝ → E)
    (hγ : ContDiff ℝ ∞ (fun x : ℝ × ℝ => γ x.1 x.2))
    (hper : ∀ t, Periodic (γ t) T)
    (hinj : ∀ t ∈ Icc a b, InjOn (γ t) (Ico 0 T))
    (hregular : ∀ t ∈ Icc a b, ∀ s, deriv (γ t) s ≠ 0) :
    ∃ Phi : ℝ → E ≃ₘ[ℝ] E,
      (∀ x, Phi a x = x) ∧ ContDiff ℝ ∞ (fun x : ℝ × E => Phi x.1 x.2) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ t x, x ∉ K → Phi t x = x) ∧
      ∀ t ∈ Icc a b, Phi t '' range (γ a) = range (γ t) := by
  let c : ℝ → sphere (0 : E) 1 → E := fun t => periodicCircleCurve T e (γ t)
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun x : ℝ × sphere (0 : E) 1 => c x.1 x.2) :=
    contMDiff_periodicCircleCurve_family hT e _ hγ hper
  have hci (t : ℝ) (ht : t ∈ Icc a b) : Injective (c t) :=
    injective_periodicCircleCurve hT e (hper t) (hinj t ht)
  have hcm (t : ℝ) (ht : t ∈ Icc a b) (q : sphere (0 : E) 1) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c t) q) := by
    have hsmooth : ContDiff ℝ ∞ (γ t) :=
      hγ.comp (f := fun s : ℝ => (t, s)) (contDiff_const.prodMk contDiff_id)
    exact mfderiv_periodicCircleCurve_injective hT e (hper t) hsmooth (hregular t ht) q
  obtain ⟨Phi, hPhi, hPhismooth, hK, hmotion⟩ :=
    exists_ambient_isotopy_of_smooth_circle_family o (sphereCircleParameter e 0)
      c hc hab hci hcm
  refine ⟨Phi, hPhi, hPhismooth, hK, ?_⟩
  intro t ht
  have hrange (s : ℝ) : range (c s) = range (γ s) :=
    range_periodicCircleCurve hT e (hper s)
  rw [← hrange a, ← hrange t, ← range_comp]
  congr 1
  funext q
  exact hmotion t ht q

end Poincare.Manifold.Schoenflies.Plane
