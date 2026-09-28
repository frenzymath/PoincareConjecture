import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.SelectedSlab
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RecutGeometry



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_terminal_planar_family_or_one_lower_end
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      Nat.card d.ends.LowerCutIndex = 1 ∨
      ∃ (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
        (K : Set E2) (χ : Real → Real),
        (∀ z x, Φ 0 z x = x) ∧
        ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2) ∧
        ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2) ∧
        IsCompact K ∧ (∀ u z x, x ∉ K → Φ u z x = x) ∧
        ContDiff Real ∞ χ ∧ (∀ z ∈ d.I, χ z = 1) ∧
        (∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z) ∧
        ∃ ρ : Real, 0 < ρ ∧ ∃ U : Set E3, IsOpen U ∧
          closedSquare ρ ⊆ e.source ∧
          (∀ x ∈ closedSquare ρ,
            (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
          (d.flatten ∘ g ∘ e) '' closedSquare ρ ⊆ U ∧
          ∀ u, EqOn (planarHeightMap Φ u) id U := by
  obtain ⟨d, hd⟩ := exists_terminal_planar_slab_or_one_lower_end
    M hg P hP hcaps hp hc hunique e he0 hep he hei hform
  rcases hd with hone | ⟨δ, hδ, _, _, K, Φ, hK, hzero, hΦ, hΦi, hfix, hmatch,
    ρ, hρ, U, hU, hsource, hmodel, hpatch, hprotected⟩
  · exact ⟨d, Or.inl hone⟩
  obtain ⟨d', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscale, _, hradius,
      _, hflatten, _, hA, hB, hI, _⟩ :=
    exists_terminal_geometry_with_smaller_end_cuts M hg P hP hcaps
      (interior_subset hp) hc e he0 hep he hei hform d hδ
  refine ⟨d', Or.inr ⟨Φ, K, fun _ => 1, hzero, hΦ, hΦi, hK, hfix,
    contDiff_const, by simp, ?_, ρ, hρ, U, hU, hsource, ?_, ?_, hprotected⟩⟩
  · intro z hz
    rw [hA, hB]
    exact hmatch z (Ioo_subset_Icc_self (hI hz))
  · simpa only [hscale, hradius] using hmodel
  · simpa only [hflatten] using hpatch

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
