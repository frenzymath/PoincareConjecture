import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Semiconcavity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem squared_distance_gap_le_upper_support_differential
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {p q z : M} {L : ℝ} (hL : 0 < L) {rho : M → ℝ}
    (hrho : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) rho q)
    (htouch : rho q = (g.edist z q).toReal)
    (hupper : ∀ᶠ x in 𝓝 q, (g.edist z x).toReal ≤ rho x)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hγ0 : γ 0 = q) (hγL : γ L = p)
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hmin : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    (g.edist z p).toReal ^ 2 - (g.edist z q).toReal ^ 2 - L ^ 2 ≤
      2 * (g.edist z q).toReal * L *
        mvfderiv (𝓡 n) rho q (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := by
  have hgd := (hγ.contMDiffAt (show (0 : ℝ) ∈ Icc 0 L from
    ⟨le_rfl, hL.le⟩)).mdifferentiableAt (by simp)
  have hrd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) rho (γ 0) := hγ0.symm ▸ hrho
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
    (hrd.hasMFDerivAt.comp 0 hgd.hasMFDerivAt)).hasDerivAt
  have hd' : HasDerivAt (fun t => rho (γ t))
      (mvfderiv (𝓡 n) rho q (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) 0 := by
    change HasDerivAt (fun t => rho (γ t))
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) rho (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) 0 at hd
    rw [hγ0] at hd
    exact hd
  have hderiv := (hd'.pow 2).sub ((hasDerivAt_id (0 : ℝ)).pow 2)
  simp only [hγ0, htouch, Nat.reduceSub, Nat.cast_ofNat, pow_one, id_eq, mul_zero, zero_mul,
    sub_zero] at hderiv
  have hmajor : ∀ᶠ t in 𝓝 (0 : ℝ),
      (g.edist z (γ t)).toReal ^ 2 - t ^ 2 ≤ rho (γ t) ^ 2 - t ^ 2 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 q) := by
      simpa only [ContinuousAt, hγ0] using hgd.continuousAt
    filter_upwards [htend.eventually hupper] with t ht
    exact sub_le_sub_right (sq_le_sq₀ ENNReal.toReal_nonneg
      (ENNReal.toReal_nonneg.trans ht) |>.2 ht) _
  have h := Poincare.Analysis.le_affine_of_concaveOn_of_upper_support hL
    (g.squared_distance_sub_sq_concave D hc hsec z hγ hspeed hmin)
    (by simp only [hγ0, htouch]) hmajor hderiv
  simp only [hγ0, hγL, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  nlinarith only [h]

theorem exists_distance_upper_support_with_common_inward_derivative
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p q z : M)
    (hgap : 0 < (g.edist z p).toReal ^ 2 - (g.edist z q).toReal ^ 2 -
      (g.edist q p).toReal ^ 2) :
    let L := (g.edist q p).toReal
    let A := (g.edist z p).toReal ^ 2 - (g.edist z q).toReal ^ 2 - L ^ 2
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ q ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho q = (g.edist z q).toReal ∧
      (∀ x ∈ U, (g.edist z x).toReal ≤ rho x) ∧
      g.inner q (D.gradient rho q) (D.gradient rho q) = 1 ∧
      ∀ (γ : ℝ → M), g.IsGeodesicOn γ (Icc 0 L) → γ 0 = q → γ L = p →
        (∀ t ∈ Icc 0 L,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        A / (2 * (g.edist z q).toReal * L) ≤
          mvfderiv (𝓡 n) rho q (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := by
  let := g.toMetricSpace
  have hqp : q ≠ p := by
    intro heq
    have hgap' : 0 < dist z p ^ 2 - dist z q ^ 2 - dist q p ^ 2 := hgap
    simp only [heq, dist_self, sub_self, zero_pow (by decide : 2 ≠ 0),
      lt_self_iff_false] at hgap'
  have hzq : z ≠ q := by
    intro heq
    have hgap' : 0 < dist z p ^ 2 - dist z q ^ 2 - dist q p ^ 2 := hgap
    simp only [heq, dist_self, zero_pow (by decide : 2 ≠ 0), sub_zero,
      sub_self, lt_self_iff_false] at hgap'
  have hL : 0 < (g.edist q p).toReal := dist_pos.mpr hqp
  have hR : 0 < (g.edist z q).toReal := dist_pos.mpr hzq
  have hsec' : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -(0 : ℝ) ≤ D.sectionalCurvature y u v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    intro y u v
    rw [neg_zero]
    apply div_nonneg (hsec y u v)
    change 0 ≤ inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2
    nlinarith only [real_inner_mul_inner_self_le u v]
  obtain ⟨U, rho, hU, hq, hrho, htouch, hupper, hunit, _⟩ :=
    g.exists_distance_hessian_upper_support D hc (K := 0) le_rfl hsec' z q hzq
  refine ⟨U, rho, hU, hq, hrho, htouch, hupper, hunit, ?_⟩
  intro γ hγ hγ0 hγL hspeed hmin
  have hrd := (hrho q hq).contMDiffAt (hU.mem_nhds hq)
  have hmajor : ∀ᶠ x in 𝓝 q, (g.edist z x).toReal ≤ rho x := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact hupper x hx
  have h := squared_distance_gap_le_upper_support_differential g D hc hsec hL
    (hrd.mdifferentiableAt (by simp)) htouch hmajor hγ hγ0 hγL hspeed hmin
  exact (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hR) hL)).2
    (by simpa only [mul_comm] using h)

end PoincareConjecture.RiemannianMetric
