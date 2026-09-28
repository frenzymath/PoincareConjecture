import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Contacts
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Intervals

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_exterior_adjacent_pairing
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hunique : ∀ q, inner Real v (f q) = inner Real v (f p) →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun z => inner Real v (f z)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      let K := connectedComponentIn
        ((fun q => inner Real v (f q)) ⁻¹' {inner Real v (f p)}) p \ e '' openSquare r
      (∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn K (e (contact r j)) ↔ i.1 = j.1) ∨
      (∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn K (e (contact r j)) ↔ i.2 = j.2) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  obtain ⟨_, a, _, has, _, _, _, _, _, r, hr, hrε, hrball,
      _, _, _, hinj, hnoncrossing⟩ :=
    exists_normalized_exterior_noncrossing_square hf hv p e he0 hep he hei hform hε
  have hrs : closedSquare r ⊆ e.source := hrball.trans (ball_subset_closedBall.trans has)
  let K := connectedComponentIn
    ((fun q => inner Real v (f q)) ⁻¹' {inner Real v (f p)}) p \ e '' openSquare r
  obtain ⟨_, hboundary, _, _, _, _⟩ :=
    compact_regular_exterior hh hunique e he0 hep hform hr hrs
  have hmem (i : Fin 2 × Fin 2) : e (contact r i) ∈ K := by
    exact (hboundary.symm.subset (mem_range_self i)).1
  let b : Fin 2 × Fin 2 → K := fun i => ⟨e (contact r i), hmem i⟩
  have hbi : Function.Injective b := fun i j hij =>
    hinj (congrArg Subtype.val hij)
  have hKlevel : K ⊆
      {q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r :=
    fun q hq => ⟨connectedComponentIn_subset _ _ hq.1, hq.2⟩
  refine ⟨r, hr, hrε, hrs, ?_⟩
  apply Poincare.Topology.pairing_of_interval_components b hbi
  · intro q hq
    obtain ⟨γ, l, u, hγ, hγe, _, hlu, hγrange, hcontacts⟩ :=
      exists_exterior_intervals_with_contacts hh hunique e he0 hep he hei hform hr hrs q hq
    exact ⟨γ, l, u, hγ.continuous, hγe.injective, hlu, hγrange, hcontacts⟩
  · intro α β hα hβ hαK hβK hα0 hα1 hβ0 hβ1
    exact hnoncrossing α β hα hβ (fun t ht => hKlevel (hαK ht))
      (fun t ht => hKlevel (hβK ht)) hα0 hα1 hβ0 hβ1

end Poincare.Manifold.Schoenflies.SaddleLevel
