import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ReflectionTubeDoubling

set_option autoImplicit false

open Set Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

theorem exists_single_period_reflection_resolving_annulus
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : ((ℝ × ℝ) × ℝ) → X)
    (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0)))) :
    ∃ (a : AddCircle (4 * L) × Icc (-d) d → X)
      (E : (AddCircle (4 * L) × Icc (-d) d) ≃ₜ squareAnnulus L d)
      (g : (ℝ × ℝ) → X),
      Topology.IsEmbedding a ∧
      Topology.IsEmbedding (fun x : squareAnnulus L d => g x) ∧
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      (∀ p, (E p : ℝ × ℝ) = annulusMap L (by linarith) (p.1, p.2)) ∧
      (∀ p, g (E p) = a p) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a ((s : AddCircle (4 * L)), u) =
          if s ≤ 2 * L then τ ((u, max |(u : ℝ)| b), s)
          else τ ((u, -max |(u : ℝ)| b), s - 2 * L)) ∧
      g '' squareAnnulus L d =
        doubledReflectionTubeMap L τ '' (strip b true '' rectangle (4 * L) d) ∧
      g '' squareAnnulus L d ⊆ τ '' singleReflectionTube L d ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) =
          (if s ≤ 2 * L then τ ((-d, d), s) else τ ((-d, -d), s - 2 * L)) ∧
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) =
          (if s ≤ 2 * L then τ ((d, d), s) else τ ((d, -d), s - 2 * L))) ∧
      squareAnnulus L d ∩ g ⁻¹' (τ '' singleReflectionTubeSide L d) =
        frontier (squareAnnulus L d) := by
  obtain ⟨hPL, _, _, hdoublefib, himage, hside⟩ :=
    doubledReflectionTubeMap_spec hcompat (by linarith) hd τ hτ hfib
  obtain ⟨a, E, g, haemb, hgemb, hgPL, hE, hgE, hperiod, hgimage, hcurves, _, _, hfront⟩ :=
    exists_reflection_resolving_annulus e hcompat hd hwidth hb hbd
      (doubledReflectionTubeMap L τ) hPL hdoublefib
  refine ⟨a, E, g, haemb, hgemb, hgPL, hE, hgE, ?_, hgimage, ?_, ?_, ?_⟩
  · intro s hs u
    simpa only [doubledReflectionTubeMap, reflectionSecondHalf] using hperiod s hs u
  · rw [hgimage, ← himage]
    apply image_mono
    rintro _ ⟨p, hp, rfl⟩
    change ((p.2 ∈ Icc (-d) d) ∧ max |p.2| b ∈ Icc (-d) d) ∧ p.1 ∈ Icc 0 (4 * L)
    exact ⟨⟨hp.2, ⟨by linarith [le_max_right |p.2| b],
      max_le (abs_le.mpr hp.2) hbd.le⟩⟩, hp.1⟩
  · intro s hs
    simpa only [doubledReflectionTubeMap, reflectionSecondHalf] using hcurves s hs
  · simpa only [hside] using hfront

end Dehn
