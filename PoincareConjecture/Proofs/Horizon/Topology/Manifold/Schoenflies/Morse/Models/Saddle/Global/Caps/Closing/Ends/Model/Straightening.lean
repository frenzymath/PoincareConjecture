import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Annulus
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.Filling.ProfileImage



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1




theorem exists_buffered_component_minimum_disk_straightening
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f q)) ⁻¹' Iio b) seed))
    (hregular : ∀ q, inner Real v (f q) = b →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {η : Real} (hη : 0 < η) :
    ∃ r ∈ Ioo (0 : Real) η, inner Real v (f p) + 2 * r ^ 2 < b ∧
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∃ δ : Real, 0 < δ ∧ ∀ (t : Real) (x : Hemisphere.Plane v), b - δ ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        D '' (f '' (d '' closedBall 0 1)) =
          quadraticMinimumCap v (inner Real v (f p)) r ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc (inner Real v (f p) + (7 * r / 8) ^ 2) b ×ˢ
                sphere (0 : Hemisphere.Plane v) r) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  have hgap : 0 < (b - inner Real v (f p)) / 4 := by linarith
  let η' := min η (Real.sqrt ((b - inner Real v (f p)) / 4))
  have hη' : 0 < η' := lt_min hη (Real.sqrt_pos.mpr hgap)
  obtain ⟨J, r, hr, _, A, D, hDheight, hDupper, _, hprofile, _, hwhole⟩ :=
    exists_buffered_capped_minimum_disk_band_straightening_of_physical_annulus_cover
      hf hv d hds hp hpb hboundary hunique e he0 hep he hei hform
      (exists_morse_disk_and_physical_annulus_cover hh d hds hp hpb hboundary hunique
        seed hcomponent hregular e he0 hep hform)
      hε T hTs γ hTcylinder hTc hTneg hη'
  have hrroot : r < Real.sqrt ((b - inner Real v (f p)) / 4) :=
    hr.2.trans_le (min_le_right _ _)
  have hr2 : r ^ 2 < (b - inner Real v (f p)) / 4 := by
    have hm := mul_pos (sub_pos.mpr hrroot)
      (add_pos (Real.sqrt_pos.mpr hgap) hr.1)
    nlinarith [Real.sq_sqrt hgap.le]
  have hsmall := image_minimum_profile_disk (inner Real v (f p)) r J f e D hprofile
  rw [hsmall] at hwhole
  exact ⟨r, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩, by nlinarith,
    A, D, hDheight, hDupper, hwhole⟩


theorem exists_component_minimum_disk_straightening
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f q)) ⁻¹' Iio b) seed))
    (hregular : ∀ q, inner Real v (f q) = b →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {η : Real} (hη : 0 < η) :
    ∃ r ∈ Ioo (0 : Real) η, inner Real v (f p) + 2 * r ^ 2 < b ∧
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v), b ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        D '' (f '' (d '' closedBall 0 1)) =
          quadraticMinimumCap v (inner Real v (f p)) r ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc (inner Real v (f p) + (7 * r / 8) ^ 2) b ×ˢ
                sphere (0 : Hemisphere.Plane v) r) := by
  obtain ⟨r, hr, hrb, A, D, hh, ⟨δ, hδ, hu⟩, hi⟩ :=
    exists_buffered_component_minimum_disk_straightening hf hv d hds hp hpb hboundary
      hunique seed hcomponent hregular e he0 hep he hei hform hε T hTs γ hTcylinder hTc hTneg hη
  exact ⟨r, hr, hrb, A, D, hh, fun t x ht => hu t x (by linarith), hi⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
