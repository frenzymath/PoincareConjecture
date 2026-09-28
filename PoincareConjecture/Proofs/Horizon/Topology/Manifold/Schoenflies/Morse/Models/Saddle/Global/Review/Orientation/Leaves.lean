import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Family
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Replacement

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem saddle_planar_family_leaf
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ data : TerminalSaddleData M P p e,
      let d := data.toTerminalSaddleGeometry
      ∃ (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
        (K : Set E2) (χ : Real → Real),
        (∀ z x, Φ 0 z x = x) ∧
        ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2) ∧
        ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2) ∧
        IsCompact K ∧ (∀ t z x, x ∉ K → Φ t z x = x) ∧
        ContDiff Real ∞ χ ∧ (∀ z ∈ d.I, χ z = 1) ∧
        (∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z) ∧
        (∀ i, planarHeightMap Φ 1 '' (d.C i ∩ d.actualBand) =
          d.modelCaps i ∩ d.modelBand) ∧
        ∃ ρ > 0, ∃ U : Set E3, IsOpen U ∧ closedSquare ρ ⊆ e.source ∧
          (∀ x ∈ closedSquare ρ,
            (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
          (d.flatten ∘ g ∘ e) '' closedSquare ρ ⊆ U ∧
          ∀ t, EqOn (planarHeightMap Φ t) id U := by
  exact Planar.exists_four_model_planar_family {
    reduction := M
    leaf := g
    leaf_mem := hg
    path := P
    protects := hP
    preserves_caps := hcaps
    point_interior := hp
    critical := hc
    unique := hunique
    chart := e
    chart_zero := he0
    chart_center := hep
    chart_smooth := he
    chart_inverse_smooth := hei
    chart_target := het
    form := hform }

theorem saddle_cap_replacement_leaf
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    {P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (K : Set E2) (χ : Real → Real)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (hK : IsCompact K)
    (hfix : ∀ t z x, x ∉ K → Φ t z x = x)
    (hχ : ContDiff Real ∞ χ)
    (hχone : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∀ H₁ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H₁ y = planarHeightMap Φ (χ (y 2)) y) →
      ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        EqOn H₂ id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ i, H₂ '' (H₁ '' data.toTerminalSaddleGeometry.C i) =
          data.toTerminalSaddleGeometry.modelCaps i := by
  exact Caps.saddle_cap_replacement M hg data Φ K χ hzero hΦ hΦinv hK hfix hχ hχone
    hplanar hlabels
end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
