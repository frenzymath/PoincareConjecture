import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathValues







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem regular_path_reducedLength_differential
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (v : TangentSpace (𝓡 n) (G.gamma Z τ)) :
    mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) (G.gamma Z τ) v =
      (K.flow.metric (0 - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(K.flow.metric 0).toRiemannianMetric⟩
  have hτ := hreg.1.choose
  have hR := hreg.1.choose_spec.choose
  have hdomain : univ ×ˢ Ioo 0 R ∈ 𝓝 (Z, τ) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hτ, hR⟩
  have hγ := (G.gamma_smooth.contMDiffAt hdomain).comp Z
    (contMDiffAt_id.prodMk contMDiffAt_const)
  change ContMDiffAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) ∞ (fun V => G.gamma V τ) Z at hγ
  have haction := (G.action_smooth.contDiffAt hdomain).comp Z
    (contDiffAt_id.prodMk contDiffAt_const)
  change ContDiffAt ℝ ∞ (fun V => G.toLExponentialFamily.action V τ) Z at haction
  have hs : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have ht : (G.gamma Z τ, τ) ∈ G.regular_chart.target :=
    G.regular_forward (Z, τ) ▸ G.regular_chart.map_source hs
  have hl := regular_reducedLength_spatial_smooth (G.regular_point _ ht)
  have heq : (fun V => reducedLength K.flow 0 p (G.gamma V τ) τ) =ᶠ[𝓝 Z]
      (fun V => (2 * Real.sqrt τ)⁻¹ * G.toLExponentialFamily.action V τ) := by
    have hn := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (G.regular_chart.open_source.mem_nhds hs)
    filter_upwards [hn] with V hV
    rw [G.reducedLength_eq_action_on_regularDomain (G.regular_source ▸ hV)]
    ring
  obtain ⟨W, hW⟩ := hreg.2.surjective v
  have hchain := congrArg (fun A => A W)
    (mvfderiv_comp Z (hl.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp)))
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    NormedSpace.fromTangentSpace] at hchain
  change fderiv ℝ (fun V => reducedLength K.flow 0 p (G.gamma V τ) τ) Z W =
    mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) (G.gamma Z τ)
      (G.toLExponentialFamily.sliceDifferential Z τ W) at hchain
  have hd := congrArg (fun A => A W) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_const_mul (haction.differentiableAt (by simp))] at hd
  simp only [smul_apply, smul_eq_mul] at hd
  rw [G.action_initial_differential Z τ hτ hR W] at hd
  have hsqrt : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have hc : (2 * Real.sqrt τ)⁻¹ * (2 * Real.sqrt τ *
      (K.flow.metric (0 - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ)
        (G.toLExponentialFamily.sliceDifferential Z τ W)) =
      (K.flow.metric (0 - τ)).inner (G.gamma Z τ) (curveVelocity (G.gamma Z) τ) v := by
    rw [hW]
    field_simp
  rw [hc] at hd
  rw [← hd, hchain]
  rw [hW]

theorem regular_path_speed_le (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain) :
    (K.flow.metric (0 - τ)).tangentNorm (G.gamma Z τ) (curveVelocity (G.gamma Z) τ) ≤
      Real.sqrt (3 * reducedLength K.flow 0 p (G.gamma Z τ) τ / τ) := by
  have hs : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have ht : (G.gamma Z τ, τ) ∈ G.regular_chart.target :=
    G.regular_forward (Z, τ) ▸ G.regular_chart.map_source hs
  have h := P.regular_reducedLength_differential_bound (G.regular_point _ ht)
    (curveVelocity (G.gamma Z) τ)
  rw [regular_path_reducedLength_differential G hreg] at h
  have hi : 0 ≤ (K.flow.metric (0 - τ)).inner (G.gamma Z τ)
      (curveVelocity (G.gamma Z) τ) (curveVelocity (G.gamma Z) τ) := by
    by_cases hv : curveVelocity (n := n) (G.gamma Z) τ = 0
    · simp [hv]
    · exact ((K.flow.metric (0 - τ)).pos _ _ hv).le
  rw [abs_of_nonneg hi] at h
  have hsq := Real.sq_sqrt hi
  change ((K.flow.metric (0 - τ)).tangentNorm (G.gamma Z τ)
    (curveVelocity (G.gamma Z) τ)) ^ 2 = _ at hsq
  have hn : 0 ≤ (K.flow.metric (0 - τ)).tangentNorm (G.gamma Z τ)
      (curveVelocity (G.gamma Z) τ) := Real.sqrt_nonneg _
  have hb := Real.sqrt_nonneg (3 * reducedLength K.flow 0 p (G.gamma Z τ) τ / τ)
  nlinarith

theorem regular_path_speed_sq_le (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ s : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ) :
    ((K.flow.metric (0 - s)).tangentNorm (G.gamma Z s) (curveVelocity (G.gamma Z) s)) ^ 2 ≤
      3 * (reducedLength K.flow 0 p (G.gamma Z τ) τ * Real.sqrt τ) /
        (s * Real.sqrt s) := by
  have hreg' := G.backward_nesting Z τ hreg s hs hsτ
  have h := P.regular_path_speed_le G hreg'
  have hl := P.reducedLength_pos p (G.gamma Z s) s hs
  have hsq := Real.sq_sqrt (by positivity :
    0 ≤ 3 * reducedLength K.flow 0 p (G.gamma Z s) s / s)
  have hn : 0 ≤ (K.flow.metric (0 - s)).tangentNorm (G.gamma Z s)
      (curveVelocity (G.gamma Z) s) := Real.sqrt_nonneg _
  have hbound : ((K.flow.metric (0 - s)).tangentNorm (G.gamma Z s)
      (curveVelocity (G.gamma Z) s)) ^ 2 ≤
      3 * reducedLength K.flow 0 p (G.gamma Z s) s / s := by
    nlinarith [Real.sqrt_nonneg (3 * reducedLength K.flow 0 p (G.gamma Z s) s / s)]
  apply hbound.trans
  have hv := P.regular_path_reducedLength_mul_sqrt_le G hreg hs hsτ
  apply (div_le_div_iff₀ hs (mul_pos hs (Real.sqrt_pos.mpr hs))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hv hs.le]

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
