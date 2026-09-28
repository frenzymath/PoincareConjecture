import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.CurvatureGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegralGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem connecting_geodesic_ricci_integral_le
    (P : AncientAsymptoticSolitonPredecessors K) (p : M)
    {τ L B scale c : ℝ} {γ : ℝ → M} {I : Set ℝ}
    (hτ : 0 < τ) (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : (K.flow.metric (0 - τ)).IsGeodesicOn γ I)
    (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, (K.flow.metric (0 - τ)).tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : (K.flow.metric (0 - τ)).edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hscale : 0 < scale)
    (hleft : reducedLength K.flow 0 p (γ 0) τ ≤ B)
    (hright : reducedLength K.flow 0 p (γ L) τ ≤ B) :
    (∫ s in (0 : ℝ)..L, (K.flow.connection (0 - τ)).ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) / c) ≤
      2 * (n : ℝ) * scale + 24 * B / (τ * scale) +
        576 / (τ ^ 2 * scale ^ 3) := by
  let g := K.flow.metric (0 - τ)
  have hB : 0 ≤ B := (P.reducedLength_pos p (γ 0) τ hτ).le.trans hleft
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I := fun s hs =>
    (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo hs).contMDiffWithinAt
  have hdist (a b : ℝ) (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) (hab : a ≤ b) :
      (g.edist (γ a) (γ b)).toReal ≤ (b - a) * c := by
    apply (g.toReal_edist_le_integral_speed hab hI
      (fun s hs => hsub ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩) hγ).trans_eq
    calc
      _ = ∫ _s in a..b, c := intervalIntegral.integral_congr (fun s hs =>
        hspeed s ⟨ha.1.trans (uIcc_of_le hab ▸ hs).1, (uIcc_of_le hab ▸ hs).2.trans hb.2⟩)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  have hsq (s : ℝ) (hs : s ∈ Icc 0 L) : g.inner (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c ^ 2 := by
    have h := congrArg (fun a : ℝ => a ^ 2) (hspeed s hs)
    dsimp only [RiemannianMetric.tangentNorm] at h
    rw [Real.sq_sqrt] at h
    · exact h
    · by_cases hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1 = 0
      · simp [hv]
      · exact (g.pos _ _ hv).le
  have hric (x : M) (s : ℝ) (r : ℝ) (hs : s ∈ Icc 0 L)
      (hx : reducedLength K.flow 0 p x τ ≤ B)
      (hd : (g.edist x (γ s)).toReal ≤ r) :
      (K.flow.connection (0 - τ)).ricci (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤
        (6 * B / τ + (72 / τ ^ 2) * r ^ 2) * c ^ 2 := by
    have h := P.ricci_intrinsic_quadratic_upper_bound p x (γ s) hτ
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
    change _ ≤ _ * g.inner _ _ _ at h
    rw [hsq s hs] at h
    apply h.trans
    have hd2 := sq_le_sq₀ ENNReal.toReal_nonneg (ENNReal.toReal_nonneg.trans hd) |>.mpr hd
    have hval := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 6 / τ)
    have hrad := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ 72 / τ ^ 2)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg c)
    convert! add_le_add hval hrad using 1 <;> ring
  have h := (K.flow.connection (0 - τ)).integral_ricci_div_speed_le_of_quadratic_endpoint_bounds
    hI hsub hgeo hL hc hspeed hmin (A := 6 * B / τ) (B := 72 / τ ^ 2)
    (by positivity) (by positivity) hscale
    (fun s hs => hric (γ 0) s (s * c) hs hleft (by
      simpa only [sub_zero] using hdist 0 s ⟨le_rfl, hL⟩ hs hs.1))
    (fun s hs => hric (γ L) s ((L - s) * c) hs hright (by
      let := g.toMetricSpace
      change dist (γ L) (γ s) ≤ _
      rw [dist_comm]
      exact hdist s L hs ⟨hL, le_rfl⟩ hs.2))
  convert! h using 1
  ring

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
