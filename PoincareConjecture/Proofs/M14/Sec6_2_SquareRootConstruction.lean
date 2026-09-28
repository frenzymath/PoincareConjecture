import PoincareConjecture.Proofs.M14.Sec6_2_SquareGaugeEndpoints










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)



theorem squarePath_contMDiffOn_of_euler
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => p.curve (s ^ 2))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  let A := Real.sqrt τ₁
  let B := Real.sqrt τ₂
  let C := Icc A B
  let γ := fun s => p.curve (s ^ 2)
  have hAB : A < B := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hγ : ContinuousOn γ C := squarePath_continuousOn p
  intro s hs
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, _⟩ := exists_smooth_gauge_lift G (γ s)
  have hnear : γ ⁻¹' U ∈ 𝓝[C] s :=
    (hγ s hs).preimage_mem_nhdsWithin (hU.mem_nhds hsU)
  obtain ⟨N, hN, hsrcN⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnear
  obtain ⟨l, r, ⟨hls, hsr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  let l' := (l + s) / 2
  let r' := (s + r) / 2
  let c := max A l'
  let d := min B r'
  have hll : l < l' := by dsimp only [l']; linarith
  have hls' : l' < s := by dsimp only [l']; linarith
  have hsr' : s < r' := by dsimp only [r']; linarith
  have hrr : r' < r := by dsimp only [r']; linarith
  have hcd : c < d := max_lt
    (lt_min hAB (hs.1.trans_lt hsr'))
    (lt_min (hls'.trans_le hs.2) (hls'.trans hsr'))
  have hsub : Icc c d ⊆ C := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ t ∈ Icc c d, γ t ∈ U := by
    intro t ht
    exact hsrcN ⟨hlr ⟨hll.trans_le ((le_max_right _ _).trans ht.1),
      (ht.2.trans (min_le_right _ _)).trans_lt hrr⟩, hsub ht⟩
  have hlocal := squareGauge_curve_contMDiffOn p b lift hCoordinates hM12 E heuler
    hU hlift hright hcd (le_max_left _ _) (min_le_left _ _) hsrc
  have hsLocal : s ∈ Icc c d := ⟨max_le hs.1 hls'.le, le_min hs.2 hsr'.le⟩
  have hLocalNear : Icc c d ∈ 𝓝[C] s := by
    apply mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hls' hsr')))
    intro t ht
    exact ⟨max_le ht.1.1 ht.2.1.le, le_min ht.1.2 ht.2.2.le⟩
  exact (hlocal s hsLocal).mono_of_mem_nhdsWithin hLocalNear



theorem squarePath_within_velocity_decomposition
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => p.curve (s ^ 2))
      (M14SqrtParameterInterval τ₁ τ₂)) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => p.curve (r ^ 2))
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ) =
      -(2 * s) • G.spacetime.timeVector (p.curve (s ^ 2)) +
        (projectedCurveVelocityWithin G (fun r => p.curve (r ^ 2))
          (M14SqrtParameterInterval τ₁ τ₂) s).val := by
  let γ := fun r => p.curve (r ^ 2)
  let C := M14SqrtParameterInterval τ₁ τ₂
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have ht := (htime.mdifferentiable (by simp) (γ s)).hasMFDerivAt.comp_hasMFDerivWithinAt s
    ((hγ s hs).mdifferentiableWithinAt (by simp)).hasMFDerivWithinAt
  have hd := ht.hasFDerivWithinAt.hasDerivWithinAt
  have hc : HasDerivWithinAt (fun r => G.spacetime.timeFunction (γ r)) (-(2 * s)) C s := by
    have hpoly : HasDerivAt (fun r : ℝ => T - r ^ 2) (-(2 * s)) s := by
      convert! (hasDerivAt_const s T).sub (hasDerivAt_pow 2 s) using 1
      simp
    exact hpoly.hasDerivWithinAt.congr_of_mem
      (fun r hr => p.curve_time _ (squarePath_parameter_mem p hr)) hs
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs
  have hclock := (hd.derivWithin hC).symm.trans (hc.derivWithin hC)
  let v := mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ C s (1 : ℝ)
  change v = -(2 * s) • G.spacetime.timeVector (γ s) +
    (G.spacetime.horizontalProjection (γ s) v).val
  rw [G.spacetime.horizontalProjection_eq]
  change v = -(2 * s) • G.spacetime.timeVector (γ s) +
    (v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s) v) •
      G.spacetime.timeVector (γ s))
  rw [show (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s) v) =
    -(2 * s) from hclock, neg_smul, sub_neg_eq_add]
  abel



noncomputable def squareRootPathOfEuler
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E) : M14SquareRootPath G p where
  curve s := p.curve (s ^ 2)
  domain := M14SqrtParameterInterval τ₁ τ₂
  interval_subset := Subset.rfl
  smooth := squarePath_contMDiffOn_of_euler p hCoordinates hM12 E heuler
  agrees _ _ := rfl
  curve_time s hs := p.curve_time _ (squarePath_parameter_mem p hs)
  horizontal_velocity := projectedCurveVelocityWithin G (fun s => p.curve (s ^ 2))
    (M14SqrtParameterInterval τ₁ τ₂)
  horizontal_agrees s hs := by
    change projectedCurveVelocityWithin G (fun r => p.curve (r ^ 2))
      (M14SqrtParameterInterval τ₁ τ₂) s = (2 * s) • p.horizontal_velocity (s ^ 2)
    unfold projectedCurveVelocityWithin
    rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
      (show M14SqrtParameterInterval τ₁ τ₂ ∈ 𝓝 s from Icc_mem_nhds hs.1 hs.2)]
    exact squarePath_projectedVelocity p hs
  derivative_eq s hs := squarePath_within_velocity_decomposition p
    (squarePath_contMDiffOn_of_euler p hCoordinates hM12 E heuler) hs

end PoincareConjecture.M14
