import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelFlow
import Mathlib.Topology.MetricSpace.Thickening












set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Manifold InnerProductSpace Topology NNReal

namespace PoincareConjecture.M25.Topology3D




theorem exists_symmetric_interval_of_nhdsSet {a b : ℝ} (hab : a ≤ b)
    {p : ℝ → Prop} (hp : ∀ᶠ z in 𝓝ˢ (Icc a b), p z) :
    ∃ d > (0 : ℝ), Icc a b ⊆ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d) ∧
      ∀ z ∈ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d), p z := by
  obtain ⟨U, hU, hIU, hpU⟩ := eventually_nhdsSet_iff_exists.mp hp
  obtain ⟨ε, hε, hεU⟩ := isCompact_Icc.exists_thickening_subset_open hU hIU
  let d := (b - a) / 2 + ε
  have hd : 0 < d := by dsimp [d]; linarith
  refine ⟨d, hd, ?_, ?_⟩
  · intro z hz
    dsimp [d]
    constructor <;> linarith [hz.1, hz.2]
  · intro z hz
    apply hpU z (hεU ?_)
    apply mem_thickening_iff.mpr
    by_cases hza : z < a
    · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hza)]
      dsimp [d] at hz
      linarith [hz.1]
    · by_cases hbz : b < z
      · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hbz)]
        dsimp [d] at hz
        linarith [hz.2]
      · exact ⟨z, ⟨le_of_not_gt hza, le_of_not_gt hbz⟩, by simpa using hε⟩





theorem exists_regular_collar_band_transport
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3)
    (a b : ℝ) (hab : a ≤ b)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ d > (0 : ℝ), Icc a b ⊆ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d) ∧
      ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        ContDiff ℝ ∞ (fun p : E3 × ℝ => Φ p.2 p.1) ∧
        (∀ y, Φ 0 y = y) ∧
        (∀ s t y, Φ (s + t) y = Φ t (Φ s y)) ∧
        (∀ t, MapsTo (Φ t) (range (fun q : UnitTwoSphere => ψ (q, 0)))
          (range (fun q : UnitTwoSphere => ψ (q, 0)))) ∧
        (∀ y ∈ range (fun q : UnitTwoSphere => ψ (q, 0)),
          ⟪u, y⟫_ℝ = (a + b) / 2 → ∀ t ∈ Ioo (-d) d,
            ⟪u, Φ t y⟫_ℝ = (a + b) / 2 + t) ∧
        (∀ y ∈ range (fun q : UnitTwoSphere => ψ (q, 0)),
          ⟪u, y⟫_ℝ ∈ Ioo ((a + b) / 2 - d) ((a + b) / 2 + d) →
            ⟪u, Φ ((a + b) / 2 - ⟪u, y⟫_ℝ) y⟫_ℝ = (a + b) / 2) := by
  obtain ⟨β, hβ, hβc, hβnear, _, F, hF, hFc, hFH, hFS⟩ :=
    exists_regular_collar_band_field ψ hψ u a b hreg
  obtain ⟨d, hd, hId, hβd⟩ := exists_symmetric_interval_of_nhdsSet hab hβnear
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds F hF hFc
  obtain ⟨Kb, Lb, hbK, hbL⟩ := compactField_bounds β hβ hβc
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 u
  let S : Set E3 := range (fun q : UnitTwoSphere => ψ (q, 0))
  have hS : ∀ y ∈ S, ∀ t, boundedFlow F hK hL y t ∈ S := by
    rintro y ⟨q, rfl⟩ t
    exact hFS K L hK hL q t
  have hHb : ∀ y ∈ S, fderiv ℝ H y (F y) = β (H y) := by
    rintro y ⟨q, rfl⟩
    simpa only [H.fderiv, H, InnerProductSpace.toDual_apply_apply] using hFH q
  let Φ := fun t => boundedFlowDiffeomorph F hK hL hF hFc t
  refine ⟨d, hd, hId, Φ, boundedFlow_contDiff F hK hL hF hFc,
    boundedFlow_zero F hK hL, ?_, ?_, ?_, ?_⟩
  · exact fun s t y => boundedFlow_add F hK hL y s t
  · exact fun t y hy => hS y hy t
  · intro y hy hym t ht
    exact regularFlow_height F hK hL β hbK hbL H
      (fun y _ => H.differentiableAt) hHb hS ((a + b) / 2) hd hβd hy hym ht
  · intro y hy hyH
    exact regularFlow_back_height F hK hL β hbK hbL H
      (fun y _ => H.differentiableAt) hHb hS ((a + b) / 2) hd hβd hy hyH

end PoincareConjecture.M25.Topology3D
