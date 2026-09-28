import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandLevels
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandTransport

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_collar_horizontal_transport
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (a b : ℝ) (hab : a ≤ b)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ d > (0 : ℝ), Icc a b ⊆ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d) ∧
      ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
        ContDiff ℝ ∞ (fun p : ℝ × E2 => Φ p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => (Φ p.1).symm p.2) ∧
        (∀ p, Φ ((a + b) / 2) p = p) ∧
        (∀ z, HasCompactSupport (fun p => Φ z p - p)) ∧
        ∀ z ∈ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d), ∀ p : E2,
          (heightPlaneCoordinates u).symm (Φ z p, z) ∈
              range (fun q : UnitTwoSphere => ψ (q, 0)) ↔
            (heightPlaneCoordinates u).symm (p, (a + b) / 2) ∈
              range (fun q : UnitTwoSphere => ψ (q, 0)) := by
  obtain ⟨β, hβ, hβc, hβnear, _, F, hF, hFc, hFH, hFS⟩ :=
    exists_regular_collar_band_field ψ hψ (u : E3) a b hreg
  obtain ⟨d, hd, hId, hβd⟩ := exists_symmetric_interval_of_nhdsSet hab hβnear
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds F hF hFc
  obtain ⟨Kb, Lb, hbK, hbL⟩ := compactField_bounds β hβ hβc
  obtain ⟨Kv, Lv, hvK, hvL⟩ := horizontalBandField_clock_bounds u F hF hFc
  let V := horizontalBandField u F
  have hV := horizontalBandField_contDiff u F hF
  have hVc := horizontalBandField_hasCompactSupport u F hFc
  let m := (a + b) / 2
  let Φ := fun z => clockEvolutionDiffeomorph V hvK hvL hV hVc m z
  have hS : ∀ y ∈ range (fun q : UnitTwoSphere => ψ (q, 0)), ∀ t,
      boundedFlow F hK hL y t ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) := by
    rintro y ⟨q, rfl⟩ t
    exact hFS K L hK hL q t
  have hHb : ∀ y ∈ range (fun q : UnitTwoSphere => ψ (q, 0)),
      ⟪(u : E3), F y⟫_ℝ = β ⟪(u : E3), y⟫_ℝ := by
    rintro y ⟨q, rfl⟩
    exact hFH q
  refine ⟨d, hd, hId, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (clockEvolution_contDiff V hvK hvL hV hVc).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  · exact (clockEvolution_contDiff V hvK hvL hV hVc).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  · exact clockEvolution_self V hvK hvL m
  · exact horizontalBandField_evolution_hasCompactSupport u F hFc hvK hvL m
  · intro z hz p
    exact horizontalBand_lift_mem_iff u F hK hL hvK hvL β hbK hbL hHb hS m hd hβd hz p

end PoincareConjecture.M25.Topology3D
