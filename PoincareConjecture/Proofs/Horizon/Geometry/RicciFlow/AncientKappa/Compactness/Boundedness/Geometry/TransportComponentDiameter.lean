import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.TransportComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.TransportDiameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem edist_transport_component_of_spherical_parametrization_le
    (g : RiemannianMetric 3 M) {u : M → ℝ}
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    {A B V : Set M} (hA : IsCompact A) (hV : IsOpen V) (hAV : A ⊆ V)
    {Q : M → M} (hQ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q V)
    (hbij : BijOn Q A B) {x : M} (hx : x ∈ A)
    {P : UnitTwoSphere → M} (hP : ContMDiff (𝓡 2) (𝓡 3) ∞ P)
    (himage : range P = connectedComponentIn A x)
    {c : ℝ} (hlevel : ∀ q, u (P q) = c)
    {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (htransport : ∀ z ∈ A, ∀ v : TangentSpace (𝓡 3) z,
      mvfderiv (𝓡 3) u z v = 0 →
      g.tangentNorm (Q z) (mfderiv (𝓡 3) (𝓡 3) Q z v) ≤ L * g.tangentNorm z v)
    (hparam : ∀ q, ∀ v : TangentSpace (𝓡 2) q,
      g.tangentNorm (P q) (mfderiv (𝓡 2) (𝓡 3) P q v) ≤
        C * (roundSphereMetric 2).tangentNorm q v)
    {y z : M} (hy : y ∈ connectedComponentIn B (Q x))
    (hz : z ∈ connectedComponentIn B (Q x)) :
    g.edist y z ≤ ENNReal.ofReal (L * C * Real.pi) := by
  have hPA (q : UnitTwoSphere) : P q ∈ A :=
    connectedComponentIn_subset A x (himage ▸ mem_range_self q)
  have hcomponents := AncientCompactness.image_connectedComponentIn_eq_of_compact_bijOn
    hA (hQ.continuousOn.mono hAV) hbij hx
  rw [← hcomponents] at hy hz
  rcases hy with ⟨y₀, hy₀, rfl⟩
  rcases hz with ⟨z₀, hz₀, rfl⟩
  rw [← himage] at hy₀ hz₀
  rcases hy₀ with ⟨q, rfl⟩
  rcases hz₀ with ⟨r, rfl⟩
  exact g.edist_transport_spherical_level_le hu hP hlevel hV hQ
    (fun q => hAV (hPA q)) hL hC (fun q => htransport (P q) (hPA q)) hparam q r

end PoincareConjecture.RiemannianMetric
