import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Conservation.Dirichlet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.GlobalBound











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

theorem cutoff_sub_le_integral_dirichletExhaustionKernel
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {η : M → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηrange : ∀ x, η x ∈ Icc 0 1) {B : ℝ} (hB : 0 ≤ B)
    (hsupport : ∀ x, 0 < η x → ∃ (U : Set M) (σ : M → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = η x ∧ (∀ y ∈ U, σ y ≤ η y) ∧ -B ≤ D.laplacian σ x)
    {t : ℝ} (ht : 0 < t) (x : M) :
    η x - B * t ≤ ∫ y, dirichletExhaustionKernel
      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y ∂g.volumeMeasure := by
  have hK := fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hmono := fun (t : ℝ) (ht : 0 < t) x y =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y
  have hbdd := fun (t : ℝ) (ht : 0 < t) x y => D.bddAbove_heatKernelContinuousTime_exhaustion
    (NeZero.pos n) hc hk hRic S hΩmono hcover ht x y
  obtain ⟨j, hj⟩ := hηc.elim_directed_cover Ω (fun j => (S j).isOpen)
    (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  apply (Dirichlet.cutoff_sub_le_integral_heatKernelContinuousTime
    D (S j) hη hηc hj hηrange hB hsupport ht x).trans
  apply integral_mono ((hK j).integrable_ambient ht x)
    (DirichletExhaustion.mass hK hmono hbdd ht x).1
  intro y
  exact DirichletExhaustion.le_supremum hbdd j ht x y

theorem integral_dirichletExhaustionKernel_eq_one
    {m : ℕ} (hm : 0 < m) {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric (m + 1) M} (D : LeviCivitaData g)
    (hc : MetricComplete g) {κ : ℝ} (hκ : 0 ≤ κ)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {t : ℝ} (ht : 0 < t) (x : M) :
    (∫ y, dirichletExhaustionKernel
      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y ∂g.volumeMeasure) = 1 := by
  have hk : 0 ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg _) hκ
  have hRic' : ∀ z (v : TangentSpace (𝓡 (m + 1)) z),
      -((m : ℝ) * κ) * g.inner z v v ≤ D.ricci z v v := by
    simpa only [neg_mul] using hRic
  have hK := fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hmono := fun (s : ℝ) (hs : 0 < s) z y =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono hs z y
  have hbdd := fun (s : ℝ) (hs : 0 < s) z y => D.bddAbove_heatKernelContinuousTime_exhaustion
    (Nat.succ_pos m) hc hk hRic' S hΩmono hcover hs z y
  apply le_antisymm (DirichletExhaustion.mass hK hmono hbdd ht x).2
  let : ConnectedSpace M := ⟨⟨x⟩⟩
  have hsupport := g.exists_distance_laplacian_upper_support D hm hc
    (Real.sqrt_nonneg κ) (by simpa only [Real.sq_sqrt hκ] using hRic)
  obtain ⟨χ, A, B, C, hA, hB, hC, hχ, hanti, hχ01, hone, hzero, hdA, hdB, hdC⟩ :=
    Poincare.Analysis.exists_radial_cutoff_profile
  have hself : g.edist x x = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  let E := fun R : ℝ => B / R ^ 2 + C * (2 * (m : ℝ) / R + (m : ℝ) * Real.sqrt κ) / R
  have hbound (R : ℝ) (hR : 0 < R) :
      1 - E R * t ≤ ∫ y, dirichletExhaustionKernel
        (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y ∂g.volumeMeasure := by
    have hs := g.radial_cutoff_lower_supports_of_distance_supports D x hχ hanti hone
      hA.le hB.le hC.le (Nat.cast_nonneg m) (Real.sqrt_nonneg κ) hR hdA hdB hdC
      (fun z hz => hsupport x z (by
        intro he; subst z; rw [hself, ENNReal.toReal_zero] at hz; linarith))
    have he := D.cutoff_sub_le_integral_dirichletExhaustionKernel hc hk hRic' S hΩmono hcover
      (hχ.continuous.comp ((g.continuous_toReal_edist x).div_const R))
      (g.hasCompactSupport_radial_cutoff hc x hR hzero) (fun z => hχ01 _)
      (B := E R) (by dsimp [E]; positivity)
      (fun z _ => by
        obtain ⟨U, σ, hU, hzU, hσ, hσeq, hσle, _, hlap⟩ := hs z
        exact ⟨U, σ, hU, hzU, hσ, hσeq, hσle, hlap⟩) ht x
    simpa only [Function.comp_apply, hself, ENNReal.toReal_zero, zero_div,
      hone 0 (by norm_num)] using he
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he : Tendsto E atTop (𝓝 0) := by
    simpa only [E, div_eq_mul_inv, inv_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_zero, zero_add, add_zero] using
      (tendsto_const_nhds.mul (hi.pow 2)).add
        ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hi).add tendsto_const_nhds)).mul hi)
  have hlim : Tendsto (fun R => 1 - E R * t) atTop (𝓝 1) := by
    simpa using (he.mul_const t).const_sub 1
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun R hR => hbound R (by linarith)⟩)

end PoincareConjecture.LeviCivitaData
