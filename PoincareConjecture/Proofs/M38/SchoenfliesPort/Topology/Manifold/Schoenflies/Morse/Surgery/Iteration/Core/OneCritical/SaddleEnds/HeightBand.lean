import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Height
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CapGap

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} (M : SphereMorseReduction f)

theorem exists_auxiliary_band_and_cap_gap
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0) :
    ∃ L : List (SphereSurgeryCoreCap (M.v : E3) g
        ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0})),
      L.Pairwise (fun D E => Disjoint
        (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) ∧
      P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ ∧
      ∃ (h : S2 → Real) (a b ε : Real),
        ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧ 0 < ε ∧
        a < inner Real (M.v : E3) (g p) - ε ∧
        inner Real (M.v : E3) (g p) + ε < b ∧
        (∀ q ∈ P.core, inner Real (M.v : E3) (g q) ∈ Ioo a b) ∧
        (∀ q ∈ P.core, h =ᶠ[𝓝 q] (fun y => inner Real (M.v : E3) (g y))) ∧
        {q | h q ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p} ∧
        (∀ D ∈ L, ∀ x ∈ closedBall (0 : E2) 1,
          ε < |inner Real (M.v : E3) (D.parametrization x) - inner Real (M.v : E3) (g p)|) ∧
        (∀ D ∈ L, ε < |D.center - inner Real (M.v : E3) (g p)|) ∧
        ∀ D ∈ L, ∀ q ∈ D.chart '' ball 0 1,
          (inner Real (M.v : E3) (g q) - D.center) / D.scale < 1 / 4 →
            h =ᶠ[𝓝 q] (fun y => inner Real (M.v : E3) (g y)) := by
  have hgEmb := M.tree.embedding_of_mem_leaves hg
  have hheight : Continuous (fun q => inner Real (M.v : E3) (g q)) :=
    (innerSL Real (M.v : E3)).continuous.comp hgEmb.contMDiff.continuous
  obtain ⟨qmin, _, hmin⟩ := P.isClosed_core.isCompact.exists_isMinOn ⟨p, hp⟩ hheight.continuousOn
  obtain ⟨qmax, _, hmax⟩ := P.isClosed_core.isCompact.exists_isMaxOn ⟨p, hp⟩ hheight.continuousOn
  let a := inner Real (M.v : E3) (g qmin) - 1
  let b := inner Real (M.v : E3) (g qmax) + 1
  let c := inner Real (M.v : E3) (g p)
  have hbounds (q : S2) (hq : q ∈ P.core) :
      inner Real (M.v : E3) (g q) ∈ Ioo a b := by
    have hl : inner Real (M.v : E3) (g qmin) ≤ inner Real (M.v : E3) (g q) := hmin hq
    have hu : inner Real (M.v : E3) (g q) ≤ inner Real (M.v : E3) (g qmax) := hmax hq
    constructor <;> dsimp [a, b] <;> linarith
  have hcp : c ∈ Ioo a b := hbounds p hp
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hP
  have hcprotected : c ∈ ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) :=
    ⟨p, (P.mfderiv_eq_on_core p hp).symm.trans hc, (P.height_eq_on_core hp).symm⟩
  obtain ⟨ε₀, hε₀, hgap, hcenters⟩ :=
    SphereSurgeryCoreCap.exists_gap_around_protected_height L hcprotected
  let ε := min ε₀ (min (c - a) (b - c)) / 2
  have hε : 0 < ε := half_pos (lt_min hε₀
    (lt_min (sub_pos.mpr hcp.1) (sub_pos.mpr hcp.2)))
  have hε₀le : ε ≤ ε₀ := by
    dsimp [ε]
    linarith [min_le_left ε₀ (min (c - a) (b - c))]
  have hεinner : ε < min (c - a) (b - c) := by
    have hm := lt_min (sub_pos.mpr hcp.1) (sub_pos.mpr hcp.2)
    dsimp [ε]
    linarith [min_le_right ε₀ (min (c - a) (b - c))]
  obtain ⟨h, hh, hgerm, hcritical, hlow, _⟩ :=
    M.exists_auxiliary_height_with_unique_critical_point hg P hP L hpair hcore hp hc a b
      ⟨hcp.1.le, hcp.2.le⟩
  refine ⟨L, hpair, hcore, h, a, b, ε, hh, hε, ?_, ?_, hbounds, hgerm, hcritical,
    fun D hD x hx => hε₀le.trans_lt (hgap D hD x hx),
    fun D hD => hε₀le.trans_lt (hcenters D hD), hlow⟩
  · have ht := hεinner.trans_le (min_le_left (c - a) (b - c))
    change a < c - ε
    linarith
  · have ht := hεinner.trans_le (min_le_right (c - a) (b - c))
    change c + ε < b
    linarith

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
