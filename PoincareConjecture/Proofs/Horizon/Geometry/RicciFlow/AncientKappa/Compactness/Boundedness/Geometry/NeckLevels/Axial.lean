import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Differential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_axial_differential_lower_bound
    {δ R G W : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hG : 0 < G) (hW : 0 ≤ W) :
    ∃ ε₀ > 0, ε₀ ≤ 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
        (_hc : MetricComplete g) (N : EpsilonNeck g), N.epsilon ≤ ε₀ →
        ∀ {f : M → ℝ}, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f →
        ∀ {C : Set M} {p : M} {H : ℝ}, p ∈ C → 0 ≤ H → H * R ^ 2 ≤ δ →
        (∀ (γ : ℝ → M) (L : ℝ), g.IsGeodesicOn γ (Icc 0 L) →
          γ 0 ∈ C → γ L ∈ C → MapsTo γ (Icc 0 L) C) →
        (∀ x ∈ C, ∀ v : TangentSpace (𝓡 3) x,
          -H * g.inner x v v ≤ D.hessian f x v v) →
        p ∉ N.coordinate_map ''
          (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) →
        ∀ {x : M}, x ∈ N.carrier → |(N.coordinate_inverse x).2| ≤ W → x ∈ C →
          (g.edist x p).toReal ≤ R → δ ≤ f x - f p →
          g.tangentNorm x (D.gradient f x) ≤ G →
          let a : TangentSpace (𝓡 3) x := N.scale⁻¹ •
            mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
              N.coordinate_map (N.coordinate_inverse x) (0, 1)
          δ / (4 * R) ≤ |mvfderiv (𝓡 3) f x a| := by
  let α := δ / (4 * R * G)
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨ε₀, hε₀, hsmall, hsegment⟩ :=
    exists_minimizing_segment_with_signed_axial_initial_part.{u} hα hW
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc N hN f hf C p H hp hH hHR hconvex hhess
    hpout x hx haxis hxC hdist hgap hgrad
  obtain ⟨L, γ, hL, hzero, hend, hγ, hspeed, hmin,
    T, hT, _, _, σ, hσ, _, halign⟩ := hsegment hc N hN hx haxis hpout
  have hLR : L ≤ R := by
    have hd := hmin 0 ⟨le_rfl, hL.le⟩ L ⟨hL.le, le_rfl⟩
    rw [hzero, hend, zero_sub, abs_neg, abs_of_pos hL] at hd
    rw [hd, ENNReal.toReal_ofReal hL.le] at hdist
    exact hdist
  have hγC : MapsTo γ (Icc 0 L) C :=
    hconvex γ L hγ (hzero ▸ hxC) (hend ▸ hp)
  have hfirst := D.mvfderiv_initial_mul_length_le_of_hessian_ge hf hL.le hγ hspeed
    (fun t ht v => hhess (γ t) (hγC ht) v)
  rw [hzero, hend] at hfirst
  have herror : H * L ^ 2 ≤ δ :=
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ hL.le hR.le |>.mpr hLR) hH).trans hHR
  have hdecrease :
      mvfderiv (𝓡 3) f x (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ≤ -δ / (2 * R) := by
    let d := mvfderiv (𝓡 3) f x (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1)
    have hdL : d * L ≤ -δ / 2 := by
      calc
        d * L ≤ f p - f x + H * L ^ 2 / 2 := hfirst
        _ ≤ -δ / 2 := by linarith only [hgap, herror]
    have hdneg : d < 0 := by
      by_contra hn
      have hh := mul_nonneg (le_of_not_gt hn) hL.le
      linarith
    have hmul := mul_le_mul_of_nonpos_left hLR hdneg.le
    apply (le_div_iff₀ (show 0 < 2 * R by positivity)).mpr
    change d * (2 * R) ≤ -δ
    nlinarith only [hdL, hmul]
  have halign0 := (halign 0 ⟨le_rfl, hT.1.le⟩).le
  rw [hzero] at halign0
  have hbound := D.abs_mvfderiv_axial_ge_of_signed_alignment f x
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) _ hσ hα.le hG.le
    halign0 hgrad (by simpa only [neg_div] using hdecrease)
  have harith : δ / (2 * R) - G * α = δ / (4 * R) := by
    dsimp [α]
    field_simp
    ring
  rwa [harith] at hbound

theorem exists_axial_differential_lower_bound_of_gap_rate
    {l G W : ℝ} (hl : 0 < l) (hG : 0 < G) (hW : 0 ≤ W) :
    ∃ ε₀ > 0, ε₀ ≤ 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
        (_hc : MetricComplete g) (N : EpsilonNeck g), N.epsilon ≤ ε₀ →
        ∀ {f : M → ℝ}, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f →
        ∀ {C : Set M} {p : M} {H : ℝ}, p ∈ C →
        (∀ (γ : ℝ → M) (L : ℝ), g.IsGeodesicOn γ (Icc 0 L) →
          γ 0 ∈ C → γ L ∈ C → MapsTo γ (Icc 0 L) C) →
        (∀ x ∈ C, ∀ v : TangentSpace (𝓡 3) x,
          -H * g.inner x v v ≤ D.hessian f x v v) →
        p ∉ N.coordinate_map ''
          (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) →
        ∀ {x : M}, x ∈ N.carrier → |(N.coordinate_inverse x).2| ≤ W → x ∈ C →
          H * (g.edist x p).toReal ≤ 2 * l →
          2 * l * (g.edist x p).toReal ≤ f x - f p →
          g.tangentNorm x (D.gradient f x) ≤ G →
          let a : TangentSpace (𝓡 3) x := N.scale⁻¹ •
            mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
              N.coordinate_map (N.coordinate_inverse x) (0, 1)
          l / 2 ≤ |mvfderiv (𝓡 3) f x a| := by
  let α := l / (2 * G)
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨ε₀, hε₀, hsmall, hsegment⟩ :=
    exists_minimizing_segment_with_signed_axial_initial_part.{u} hα hW
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc N hN f hf C p H hp hconvex hhess
    hpout x hx haxis hxC herror hgap hgrad
  obtain ⟨L, γ, hL, hzero, hend, hγ, hspeed, hmin,
    T, hT, _, _, σ, hσ, _, halign⟩ := hsegment hc N hN hx haxis hpout
  have hlength : (g.edist x p).toReal = L := by
    have hd := hmin 0 ⟨le_rfl, hL.le⟩ L ⟨hL.le, le_rfl⟩
    rw [hzero, hend, zero_sub, abs_neg, abs_of_pos hL] at hd
    rw [hd, ENNReal.toReal_ofReal hL.le]
  rw [hlength] at herror hgap
  have hγC : MapsTo γ (Icc 0 L) C :=
    hconvex γ L hγ (hzero ▸ hxC) (hend ▸ hp)
  have hfirst := D.mvfderiv_initial_mul_length_le_of_hessian_ge hf hL.le hγ hspeed
    (fun t ht v => hhess (γ t) (hγC ht) v)
  rw [hzero, hend] at hfirst
  have hdecrease :
      mvfderiv (𝓡 3) f x (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ≤ -l := by
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      mvfderiv (𝓡 3) f x (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) * L ≤
          f p - f x + H * L ^ 2 / 2 := hfirst
      _ ≤ -l * L := by nlinarith [mul_le_mul_of_nonneg_right herror hL.le]
  have halign0 := (halign 0 ⟨le_rfl, hT.1.le⟩).le
  rw [hzero] at halign0
  have hbound := D.abs_mvfderiv_axial_ge_of_signed_alignment f x
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) _ hσ hα.le hG.le halign0 hgrad hdecrease
  have harith : l - G * α = l / 2 := by
    dsimp [α]
    field_simp
    ring
  rwa [harith] at hbound

end PoincareConjecture.EpsilonNeck
