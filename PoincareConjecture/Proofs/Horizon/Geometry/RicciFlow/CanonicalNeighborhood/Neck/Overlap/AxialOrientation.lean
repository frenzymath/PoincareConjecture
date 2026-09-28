import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_transition_band_orientation :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ (S : Set ℝ), IsPreconnected S →
        S ⊆ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ S → N'.coordinate_map (q, s) ∈ N.carrier) →
        (∃ a ∈ S, ∃ b ∈ S, a < b) →
          let f := fun (q : UnitTwoSphere) (t : ℝ) =>
            (N.coordinate_inverse (N'.coordinate_map (q, t))).2
          (∀ q, StrictMonoOn (f q) S) ∨ (∀ q, StrictAntiOn (f q) S) := by
  obtain ⟨ε₀, hε₀, hsmall, hmono⟩ := exists_transition_axis_monotonicity.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' S hS hdom hcarrier ⟨a, ha, b, hb, hab⟩
  let f := fun (q : UnitTwoSphere) (t : ℝ) =>
    (N.coordinate_inverse (N'.coordinate_map (q, t))).2
  have hline (q : UnitTwoSphere) : StrictMonoOn (f q) S ∨ StrictAntiOn (f q) S :=
    (hmono N N' hN hN' q S hS hdom (hcarrier q)).1
  have hcont (s : ℝ) (hs : s ∈ S) : Continuous (fun q : UnitTwoSphere => f q s) := by
    have hmap : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (q, s))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hcarrier q s hs))).comp q
          (N'.coordinateSlice_contMDiff (hdom hs) q)
    exact hmap.continuous.snd
  have hne (q : UnitTwoSphere) (_ : q ∈ (univ : Set UnitTwoSphere)) :
      f q b - f q a ≠ 0 := by
    rcases hline q with h | h
    · exact (sub_pos.mpr (h ha hb hab)).ne'
    · exact (sub_neg.mpr (h ha hb hab)).ne
  rcases isPreconnected_univ.mapsTo_Ioi_or_Iio
      ((hcont b hb).sub (hcont a ha)).continuousOn hne with hpos | hneg
  · left
    intro q
    rcases hline q with h | h
    · exact h
    · have hp : 0 < f q b - f q a := hpos (mem_univ q)
      have hn := h ha hb hab
      linarith
  · right
    intro q
    rcases hline q with h | h
    · have hn : f q b - f q a < 0 := hneg (mem_univ q)
      have hp := h ha hb hab
      linarith
    · exact h

end PoincareConjecture.EpsilonNeck
