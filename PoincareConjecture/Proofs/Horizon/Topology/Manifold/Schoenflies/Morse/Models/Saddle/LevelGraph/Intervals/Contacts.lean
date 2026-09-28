import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Parametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Connected.IntervalEndpoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_exterior_intervals_with_contacts
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∀ q ∈ K, ∃ (γ : Real → S2) (a b : Real),
      ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ γ ∧ Topology.IsEmbedding γ ∧
      (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) γ t)) ∧
      a < b ∧ γ '' Icc a b = connectedComponentIn K q ∧
      range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∩ connectedComponentIn K q =
        {γ a, γ b} := by
  obtain ⟨H, _, _, hgerm, hKL, harcs⟩ :=
    exists_exterior_interval_parametrizations hh hunique e he0 hep he hei hform hr hrs
  obtain ⟨_, hlocal, hcontacts⟩ :=
    exterior_completion_boundary hh hunique e he0 hep he hei hform hr hrs H hgerm
  dsimp only
  intro q hq
  obtain ⟨γ, a, b, z, hγ, hγe, hγd, hab, hγJ, hz, hγr⟩ := harcs q hq
  refine ⟨γ, a, b, hγ, hγe, hγd, hab, hγJ, ?_⟩
  apply Poincare.Topology.inter_connectedComponentIn_eq_interval_endpoints
    hKL hz hγe hab hγJ hγr hlocal
  intro x hx
  obtain ⟨δ, α, hδ, hα, hα0, _, hαL, hαK⟩ := hcontacts x hx
  exact ⟨δ, hδ, α, hα, hα0, hαL, hαK⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
