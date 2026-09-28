import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.SignedSegments
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Differential










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CylinderCover




theorem exists_axial_differential_lower_bound_of_gap_rate
    {l G W : ℝ} (hl : 0 < l) (hG : 0 < G) (hW : 0 ≤ W) :
    ∃ ε₀ > 0, ε₀ ≤ 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (_hc : MetricComplete g)
        (Φ : RoundCylinderSpace → M) {ε r : ℝ}, 0 < ε → 0 < r → ε ≤ ε₀ →
        IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
          (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
        (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
          Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
        RoundCylinderClose ε 0
          (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w) →
        ∀ {u : M → ℝ}, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u →
        ∀ {C : Set M} {p : M} {H : ℝ}, p ∈ C →
        (∀ (γ : ℝ → M) (L : ℝ), g.IsGeodesicOn γ (Icc 0 L) →
          γ 0 ∈ C → γ L ∈ C → MapsTo γ (Icc 0 L) C) →
        (∀ x ∈ C, ∀ v : TangentSpace (𝓡 3) x,
          -H * g.inner x v v ≤ D.hessian u x v v) →
        p ∉ Φ '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) →
        ∀ {z : RoundCylinderSpace}, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → |z.2| ≤ W → Φ z ∈ C →
          H * (g.edist (Φ z) p).toReal ≤ 2 * l →
          2 * l * (g.edist (Φ z) p).toReal ≤ u (Φ z) - u p →
          g.tangentNorm (Φ z) (D.gradient u (Φ z)) ≤ G →
          l / 2 ≤ |mvfderiv (𝓡 3) u (Φ z)
            (r⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z (0, 1))| := by
  let α := l / (2 * G)
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨ε₀, hε₀, hsmall, hsegment⟩ :=
    exists_minimizing_segment_with_signed_axial_initial_direction.{u} hα hW
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc Φ ε r hε hr hεsmall hΦ hfiber hclose
    u hu C p H hp hconvex hhess hpout z hz haxis hzC herror hgap hgrad
  obtain ⟨a, ha, hvalue, _, _⟩ := exists_projectiveCylinderSlab_axialCoordinate Φ hΦ
    (fun z hz w hw => hfiber z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
      w ⟨hw.1, hw.2.1.le, hw.2.2.le⟩)
  obtain ⟨L, γ, hL, hzero, hend, hγ, hspeed, hmin, σ, hσ, halign⟩ :=
    hsegment g D hc Φ hε hr hεsmall hΦ hclose ha hvalue hz haxis hpout
  have hlength : (g.edist (Φ z) p).toReal = L := by
    have hd := hmin 0 ⟨le_rfl, hL.le⟩ L ⟨hL.le, le_rfl⟩
    rw [hzero, hend, zero_sub, abs_neg, abs_of_pos hL] at hd
    rw [hd, ENNReal.toReal_ofReal hL.le]
  rw [hlength] at herror hgap
  have hγC : MapsTo γ (Icc 0 L) C :=
    hconvex γ L hγ (hzero ▸ hzC) (hend ▸ hp)
  have hfirst := D.mvfderiv_initial_mul_length_le_of_hessian_ge hu hL.le hγ hspeed
    (fun t ht v => hhess (γ t) (hγC ht) v)
  rw [hzero, hend] at hfirst
  have hdecrease : mvfderiv (𝓡 3) u (Φ z)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ≤ -l := by
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      mvfderiv (𝓡 3) u (Φ z) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) * L ≤
          u p - u (Φ z) + H * L ^ 2 / 2 := hfirst
      _ ≤ -l * L := by nlinarith [mul_le_mul_of_nonneg_right herror hL.le]
  have hbound := D.abs_mvfderiv_axial_ge_of_signed_alignment u (Φ z)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) _ hσ hα.le hG.le halign.le hgrad hdecrease
  have harith : l - G * α = l / 2 := by
    dsimp [α]
    field_simp
    ring
  rwa [harith] at hbound

end PoincareConjecture.CylinderCover
