import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Radial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.LeviCivitaData.abs_mvfderiv_endpoint_pair_le_of_hessian_le_with_gap
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f h : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r η C : ℝ}
    (hr : 0 ≤ r) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hpair : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) ≤ η)
    (hhessf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v)
    (hhessh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian h (γ t) v v ≤ C * g.inner (γ t) v v)
    :
    |mvfderiv (𝓡 n) f (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)| ≤
        2 * η * r + |f (γ 1) - f (γ 0)| + C * r ^ 2 / 2 ∧
      |mvfderiv (𝓡 n) h (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)| ≤
        2 * η * r + |f (γ 1) - f (γ 0)| + C * r ^ 2 / 2 := by
  let V := fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  let F := fun t => mvfderiv (𝓡 n) f (γ t) (V t)
  let H := fun t => mvfderiv (𝓡 n) h (γ t) (V t)
  have hdf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => f (γ s)) (F t) t := by
    exact (((hf.contMDiffAt (hU.mem_nhds (hγU ht))).mdifferentiableAt
      (by simp)).hasMFDerivAt.comp t
      ((hγ.contMDiffAt ht).mdifferentiableAt (by simp)).hasMFDerivAt
      ).hasFDerivAt.hasDerivAt
  have hdh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => h (γ s)) (H t) t := by
    exact (((hh.contMDiffAt (hU.mem_nhds (hγU ht))).mdifferentiableAt
      (by simp)).hasMFDerivAt.comp t
      ((hγ.contMDiffAt ht).mdifferentiableAt (by simp)).hasMFDerivAt
      ).hasFDerivAt.hasDerivAt
  have hsum (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |F t + H t| ≤ η * r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have heq : g.inner (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) (V t) =
        F t + H t := by
      rw [map_add, add_apply, D.inner_gradient, D.inner_gradient]
    rw [← heq]
    calc
      _ ≤ g.tangentNorm (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) *
          g.tangentNorm (γ t) (V t) :=
        abs_real_inner_le_norm (D.gradient f (γ t) + D.gradient h (γ t)) (V t)
      _ ≤ η * r := by
        rw [hspeed t ht]
        exact mul_le_mul_of_nonneg_right (hpair t ht) hr
  have hend := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => ((hdf t ht).add (hdh t ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hsum t ht)
    (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  have hdiff : |(f (γ 1) + h (γ 1)) - (f (γ 0) + h (γ 0))| ≤ η * r := by
    simpa only [Pi.add_apply, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hend
  have hF := D.mvfderiv_endpoint_le_of_hessian_le hU hf hγ hγU hspeed hhessf
  have hH := D.mvfderiv_endpoint_le_of_hessian_le hU hh hγ hγU hspeed hhessh
  have hsum1 := abs_le.mp (hsum 1 (by simp))
  have hdiff1 := abs_le.mp hdiff
  have hηr : 0 ≤ η * r := mul_nonneg hη hr
  have hCr : 0 ≤ C * r ^ 2 / 2 := by positivity
  change F 1 ≤ _ at hF
  change H 1 ≤ _ at hH
  have hfdiff := abs_le.mp (le_refl |f (γ 1) - f (γ 0)|)
  change |F 1| ≤ _ ∧ |H 1| ≤ _
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

open Set Filter
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.LeviCivitaData.abs_mvfderiv_endpoint_pair_le_of_hessian_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f h : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r η C : ℝ}
    (hr : 0 ≤ r) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hpair : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) ≤ η)
    (hhessf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v)
    (hhessh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian h (γ t) v v ≤ C * g.inner (γ t) v v)
    (hlevel : f (γ 1) = f (γ 0)) :
    |mvfderiv (𝓡 n) f (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)| ≤
        2 * η * r + C * r ^ 2 / 2 ∧
      |mvfderiv (𝓡 n) h (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)| ≤
        2 * η * r + C * r ^ 2 / 2 := by
  have hb := D.abs_mvfderiv_endpoint_pair_le_of_hessian_le_with_gap
    hU hf hh hγ hγU hr hη hC hspeed hpair hhessf hhessh
  simpa only [hlevel, sub_self, abs_zero, add_zero] using hb

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_distance_upper_support_gradient_pair_abs_le_with_gap
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    {V : Set M} (hV : IsOpen V) {f h : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f V)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h V)
    (hγV : MapsTo γ (Icc 0 1) V) {η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hpair : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) ≤ η)
    (hhessf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v)
    (hhessh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian h (γ t) v v ≤ C * g.inner (γ t) v v)
    :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ γ 1 ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal ∧
      (∀ y ∈ U, (g.edist (γ 0) y).toReal ≤ rho y) ∧
      D.gradient rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal⁻¹ •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 ∧
      g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient rho (γ 1)) = 1 ∧
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient f (γ 1))| ≤
        2 * η + |f (γ 1) - f (γ 0)| / (g.edist (γ 0) (γ 1)).toReal +
          C * (g.edist (γ 0) (γ 1)).toReal / 2 ∧
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient h (γ 1))| ≤
        2 * η + |f (γ 1) - f (γ 0)| / (g.edist (γ 0) (γ 1)).toReal +
          C * (g.edist (γ 0) (γ 1)).toReal / 2 := by
  obtain ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit⟩ :=
    g.exists_distance_radial_upper_support_on_minimizing_segment D hc hγ hneq hmin
  let d := (g.edist (γ 0) (γ 1)).toReal
  have hd : 0 < d := by
    let := g.toMetricSpace
    exact dist_pos.mpr hneq
  have hsq : g.inner (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) = d ^ 2 := by
    have hu := hunit
    simp only [hgrad, map_smul, smul_apply, smul_eq_mul] at hu
    change d⁻¹ * (d⁻¹ * _) = 1 at hu
    field_simp [hd.ne'] at hu
    nlinarith
  have hspeed1 : g.tangentNorm (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) = d := by
    change Real.sqrt _ = d
    rw [hsq, Real.sqrt_sq hd.le]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = d := by
    have hb := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hγ.hasDerivAt_tangentNorm_zero hs).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ))) (by simp : (1 : ℝ) ∈ Icc 0 1) ht
    have heq : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) =
        g.tangentNorm (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hb
    exact heq.trans hspeed1
  obtain ⟨hfbound, hhbound⟩ := D.abs_mvfderiv_endpoint_pair_le_of_hessian_le_with_gap
    hV hf hh hγ hγV hd.le hη hC hspeed hpair hhessf hhessh
  have htransfer (φ : M → ℝ)
      (hb : |mvfderiv (𝓡 n) φ (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)| ≤
        2 * η * d + |f (γ 1) - f (γ 0)| + C * d ^ 2 / 2) :
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient φ (γ 1))| ≤
        2 * η + |f (γ 1) - f (γ 0)| / d + C * d / 2 := by
    rw [hgrad, map_smul, smul_apply, smul_eq_mul, g.symm, D.inner_gradient,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ d⁻¹ * (2 * η * d + |f (γ 1) - f (γ 0)| + C * d ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
      _ = 2 * η + |f (γ 1) - f (γ 0)| / d + C * d / 2 := by field_simp
  exact ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit,
    htransfer f hfbound, htransfer h hhbound⟩

theorem exists_distance_upper_support_gradient_pair_abs_le
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    {V : Set M} (hV : IsOpen V) {f h : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f V)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h V)
    (hγV : MapsTo γ (Icc 0 1) V) {η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hpair : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (D.gradient f (γ t) + D.gradient h (γ t)) ≤ η)
    (hhessf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v)
    (hhessh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian h (γ t) v v ≤ C * g.inner (γ t) v v)
    (hlevel : f (γ 1) = f (γ 0)) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ γ 1 ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal ∧
      (∀ y ∈ U, (g.edist (γ 0) y).toReal ≤ rho y) ∧
      D.gradient rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal⁻¹ •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 ∧
      g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient rho (γ 1)) = 1 ∧
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient f (γ 1))| ≤
        2 * η + C * (g.edist (γ 0) (γ 1)).toReal / 2 ∧
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient h (γ 1))| ≤
        2 * η + C * (g.edist (γ 0) (γ 1)).toReal / 2 := by
  obtain ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit, hfbound, hhbound⟩ :=
    g.exists_distance_upper_support_gradient_pair_abs_le_with_gap D hc hγ hneq hmin
      hV hf hh hγV hη hC hpair hhessf hhessh
  refine ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit, ?_, ?_⟩
  · simpa only [hlevel, sub_self, abs_zero, zero_div, add_zero] using hfbound
  · simpa only [hlevel, sub_self, abs_zero, zero_div, add_zero] using hhbound

end PoincareConjecture.RiemannianMetric
