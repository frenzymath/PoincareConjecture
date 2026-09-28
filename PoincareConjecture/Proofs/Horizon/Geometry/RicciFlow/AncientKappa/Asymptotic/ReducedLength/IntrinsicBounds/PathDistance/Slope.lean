import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathSpeed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.DistanceSupport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathDistance.Scale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.MovingEndpoints.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open ReducedLengthBounds

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem regular_path_reducedLength_le_endpoint_bound
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ s A : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ)
    (hend : reducedLength K.flow 0 p (G.gamma Z τ) τ ≤ A) :
    reducedLength K.flow 0 p (G.gamma Z s) s ≤ A * Real.sqrt τ / Real.sqrt s := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
  exact (P.regular_path_reducedLength_mul_sqrt_le G hreg hs hsτ).trans
    (mul_le_mul_of_nonneg_right hend (Real.sqrt_nonneg τ))

theorem regular_path_speed_le_twice_scale
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ s A : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ) (hA : 1 ≤ A)
    (hend : reducedLength K.flow 0 p (G.gamma Z τ) τ ≤ A) :
    (K.flow.metric (-s)).tangentNorm (G.gamma Z s) (curveVelocity (G.gamma Z) s) ≤
      2 * pathDistanceScale A τ s := by
  have h := P.regular_path_speed_sq_le G hreg hs hsτ
  rw [zero_sub] at h
  have hbound : 3 * (reducedLength K.flow 0 p (G.gamma Z τ) τ * Real.sqrt τ) /
      (s * Real.sqrt s) ≤ 3 * (A * Real.sqrt τ / (s * Real.sqrt s)) := by
    have hh := mul_le_mul_of_nonneg_right hend (Real.sqrt_nonneg τ)
    have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : 0 ≤ (3 : ℝ)))
      (mul_nonneg hs.le (Real.sqrt_nonneg s))
    exact hh'.trans_eq (by ring)
  have hsq := pathDistanceScale_sq (by linarith : 0 ≤ A) (hs.trans_le hsτ).le hs
  have hc := pathDistanceScale_pos (by linarith : 0 < A) (hs.trans_le hsτ) hs
  nlinarith [h.trans hbound]

theorem regular_paths_eventually_distance_slope_lt
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z W : TangentSpace (𝓡 n) p} {τ s A r : ℝ}
    (hZ : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hW : (W, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ) (hA : 1 ≤ A)
    (hendZ : reducedLength K.flow 0 p (G.gamma Z τ) τ ≤ A)
    (hendW : reducedLength K.flow 0 p (G.gamma W τ) τ ≤ A)
    (hr : (2 * (n : ℝ) + 604) * pathDistanceScale A τ s < r) :
    ∀ᶠ t in 𝓝[>] s,
      slope (fun t => ((K.flow.metric (-t)).edist (G.gamma Z t) (G.gamma W t)).toReal) s t < r := by
  have hτ := hZ.1.choose
  have hR := hZ.1.choose_spec.choose
  have hgam (V : TangentSpace (𝓡 n) p) :
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (G.gamma V) (Ioo 0 R) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(K.flow.metric 0).toRiemannianMetric⟩
    intro t ht
    exact ((G.gamma_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ V, ht⟩)).comp t
        (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
  have htime : -s ∈ interior (Iic (0 : ℝ)) := by
    rw [interior_Iic]
    exact neg_neg_of_pos hs
  have hc := pathDistanceScale_pos (by linarith : 0 < A) hτ hs
  obtain ⟨u, d, hu, hupper, hd, hdb⟩ := P.exists_backward_distance_upper_support_at_pair
    p (G.gamma Z s) (G.gamma W s) hs hc
    (P.regular_path_reducedLength_le_endpoint_bound G hZ hs hsτ hendZ)
    (P.regular_path_reducedLength_le_endpoint_bound G hW hs hsτ hendW)
  apply K.flow.eventually_moving_distance_slope_lt isOpen_Ioo (hgam Z) (hgam W)
    htime ⟨hs, hsτ.trans_lt hR⟩ hu hupper hd
  have hd' := hdb.trans (pathDistanceScale_ricci_coefficient_le (n := n) hA hs hsτ)
  have hvZ := P.regular_path_speed_le_twice_scale G hZ hs hsτ hA hendZ
  have hvW := P.regular_path_speed_le_twice_scale G hW hs hsτ hA hendW
  change _ + (K.flow.metric (-s)).tangentNorm _ (curveVelocity (G.gamma Z) s) +
    (K.flow.metric (-s)).tangentNorm _ (curveVelocity (G.gamma W) s) < r
  nlinarith

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
