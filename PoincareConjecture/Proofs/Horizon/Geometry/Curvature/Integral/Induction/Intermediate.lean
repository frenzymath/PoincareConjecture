import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.LevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}

theorem integral_scalarCurvature_posPart_slab_le_of_scaled_level_induction
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α C κ : ℝ} (ha : 0 < a) (hab : a < b)
    (hm : 2 ≤ m + 1) (hα : 0 < α) (hC : 0 ≤ C) (hslab : Icc a b ⊆ I)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a b, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -K x ≤ D.sectionalCurvature x v w)
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t ≤ α * t ^ (m + 1))
    (hhess : ∀ t ∈ Icc a b, ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a b,
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    let DL := fun t => (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g).leviCivitaData
    (∀ t ∈ Icc a b,
      (∫ z, max 0 ((DL t).scalarCurvature z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
      C * (κ + ∫ z, D.levelSectionalError f K (α / t) (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (α * C + ((m + 2 : ℕ) : ℝ) ^ 2) *
        (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
      2 * α * C * (κ * (b - a) +
        (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) * b ^ m) +
      2 * ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3) * b ^ m -
        2 * deriv (g.regularLevelArea hf) b := by
  let U := g.regularDomain hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  let (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
  let (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
  let DL := fun t => (RiemannianMetric.regularLevelMetric
    hf U (g.regularDomain_regular hf) t g).leviCivitaData
  dsimp only
  intro hind
  let μ := fun t => g.regularLevelVolume hf U (g.regularDomain_regular hf) t
  let A := g.regularLevelArea hf
  let S := fun x => D.scalarCurvature x -
    2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) + D.levelGaussTerm f x
  let W := fun t => ∫ z, max 0 ((DL t).scalarCurvature z) /
    g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z)) ∂μ t
  let J := fun t => ∫ z, K (openLevelIncl f U t z) ∂μ t
  let N := fun t => ∫ z, max 0 (-D.levelMeanCurvature f (openLevelIncl f U t z)) ∂μ t
  let E := fun t => ∫ z,
    D.levelSectionalError f K (α / t) (openLevelIncl f U t z) ∂μ t
  have hc := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hU : f ⁻¹' Icc a b ⊆ U := fun x hx =>
    (g.mem_regularDomain_iff hf x).mpr (hreg x (hslab hx))
  have hUq : (U : Set M) ⊆ {x | 0 < D.levelQ f x} :=
    fun _ hx => Real.sqrt_pos.mp hx
  have hSc : ContinuousOn S U :=
    (D.continuous_scalarCurvature.continuousOn.sub
      ((D.continuousOn_ricci_levelUnitNormal hf).mono hUq |>.const_mul 2)).add
      ((D.continuousOn_levelGaussTerm hf).mono hUq)
  have hSquot : ContinuousOn
      (fun x => max 0 (S x) / g.tangentNorm x (g.gradient f x)) U :=
    ((continuousOn_const (c := (0 : ℝ))).sup hSc).div
      (g.continuous_tangentNorm_gradient hf).continuousOn (fun _ hx => ne_of_gt hx)
  have hscalar (t : ℝ) (z : openLevelSet f U t) :
      (DL t).scalarCurvature z = S (openLevelIncl f U t z) :=
    D.regularLevel_scalarCurvature_gauss g hf U (g.regularDomain_regular hf) t (DL t) z
  have hWc : ContinuousOn W (Icc a b) := by
    apply (g.continuousOn_regularLevelIntegral_compact_slab hf U
      (g.regularDomain_regular hf) hc hU hSquot).congr
    intro t _
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hscalar]
  have hJc : ContinuousOn J (Icc a b) :=
    g.continuousOn_regularLevelIntegral_compact_slab hf U
      (g.regularDomain_regular hf) hc hU hKc
  have hNc : ContinuousOn N (Icc a b) :=
    g.continuousOn_regularLevelIntegral_compact_slab hf U
      (g.regularDomain_regular hf) hc hU
      ((continuousOn_const (c := (0 : ℝ))).sup
        (D.continuousOn_levelMeanCurvature_regularDomain hf).neg)
  have hAc : ContinuousOn A (Icc a b) :=
    (D.first_variation_regularLevelArea hf hI hproper hreg).1.continuousOn.mono hslab
  have hβc : ContinuousOn (fun t : ℝ => α / t) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  have hEc : ContinuousOn E (Icc a b) := by
    apply (hJc.add ((hNc.add ((hβc.const_mul (m + 1 : ℕ)).mul hAc)).mul hβc)).congr
    intro t ht
    exact D.integral_levelSectionalError_eq hf hI hproper hreg (hslab ht) hKc (α / t)
  have hWi := hWc.integrableOn_compact isCompact_Icc (μ := volume)
  have hEi := ((continuousOn_const (c := κ)).add hEc).integrableOn_compact
    isCompact_Icc (μ := volume)
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : W t ≤ α * C * (κ + E t) := by
    have hw := D.integral_regularLevel_scalarCurvature_posPart_div_speed_le
      hf hI hproper hreg (hslab ht) hα
      (fun x hx => (hspeed x (by change f x ∈ Icc a b; rwa [hx])).1)
    have hi := mul_le_mul_of_nonneg_left (hind t ht) hα.le
    dsimp only at hw
    change W t ≤ _ at hw
    change α * _ ≤ α * (C * (κ + E t)) at hi
    exact hw.trans (by simpa only [mul_assoc] using hi)
  have hweighted := setIntegral_mono_on hWi (hEi.const_mul (α * C)) measurableSet_Icc hpoint
  rw [integral_const_mul] at hweighted
  have herr₀ := D.integral_regularLevel_sectionalError_le_with_scale
    hf hI hproper hreg ha hab.le hm hα hslab hKc hK harea hhess hspeed
  change (∫ t in Icc a b, 1 + E t) ≤ _ at herr₀
  have hEi₀ := hEc.integrableOn_compact isCompact_Icc (μ := volume)
  have hi₁ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) volume :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hiκ : IntegrableOn (fun _ : ℝ => κ) (Icc a b) volume :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hshift : (∫ t in Icc a b, κ + E t) =
      (κ - 1) * (b - a) + ∫ t in Icc a b, 1 + E t := by
    rw [integral_add hiκ hEi₀, integral_add hi₁ hEi₀]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply_univ]
    rw [← Measure.real, Real.volume_real_Icc_of_le hab.le]
    ring
  have herr : (∫ t in Icc a b, κ + E t) ≤
      (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
        (κ * (b - a) + (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) * b ^ m) := by
    simp only [Nat.add_sub_cancel] at herr₀
    rw [hshift]
    nlinarith only [herr₀]
  have hlevels : (∫ t in Icc a b, W t) ≤ α * C *
      ((∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
        (κ * (b - a) + (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) * b ^ m)) :=
    hweighted.trans (mul_le_mul_of_nonneg_left herr (mul_nonneg hα.le hC))
  have hendpoint (t : ℝ) (ht : t ∈ Icc a b) : (α / t) * A t ≤ α ^ 2 * b ^ m := by
    have htpos : 0 < t := ha.trans_le ht.1
    have hbnd := Poincare.CurvatureIntegral.area_mul_reciprocal_le_pow htpos
      (by omega : 1 ≤ m + 1) hα.le (harea t ht)
    simp only [Nat.add_sub_cancel] at hbnd
    rw [mul_comm] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ htpos.le ht.2 m) (sq_nonneg α))
  have hleft := mul_le_mul_of_nonneg_left (hendpoint a ⟨le_rfl, hab.le⟩)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (m + 1)))
  have hright := mul_le_mul_of_nonneg_left (hendpoint b ⟨hab.le, le_rfl⟩)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Nat.cast_nonneg (m + 1))) hα.le)
  have hboundary := D.integral_scalarCurvature_posPart_le_regularLevels_area
    hf hI hproper hreg hab hslab hα (div_nonneg hα.le ha.le)
    (div_nonneg hα.le (ha.trans hab).le) (hKc.mono hU) hK hsec
    (hhess a ⟨le_rfl, hab.le⟩) (hhess b ⟨hab.le, le_rfl⟩)
    (fun x hx => hspeed x (by change f x ∈ Icc a b; rw [hx]; exact ⟨hab.le, le_rfl⟩))
  dsimp only at hboundary
  change (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
    2 * (∫ t in Icc a b, W t) +
    2 * ((m + 2 : ℕ) : ℝ) ^ 2 * (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
    2 * ((m + 1 : ℕ) : ℝ) * (α / a) * A a +
    2 * ((m + 1 : ℕ) : ℝ) * α * (α / b) * A b - 2 * deriv A b at hboundary
  change (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
    2 * (α * C + ((m + 2 : ℕ) : ℝ) ^ 2) *
      (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
    2 * α * C * (κ * (b - a) +
        (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) * b ^ m) +
      2 * ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3) * b ^ m - 2 * deriv A b
  nlinarith only [hboundary, hlevels, hleft, hright]

theorem integral_scalarCurvature_posPart_slab_le_of_level_induction
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α C : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hm : 2 ≤ m + 1) (hα : 0 < α) (hC : 0 ≤ C) (hslab : Icc a b ⊆ I)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a b, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -K x ≤ D.sectionalCurvature x v w)
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t ≤ α * t ^ (m + 1))
    (hhess : ∀ t ∈ Icc a b, ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a b,
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    let DL := fun t => (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g).leviCivitaData
    (∀ t ∈ Icc a b,
      (∫ z, max 0 ((DL t).scalarCurvature z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
      C * (1 + ∫ z, D.levelSectionalError f K (α / t) (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (α * C + ((m + 2 : ℕ) : ℝ) ^ 2) *
        (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
      2 * α * C * (1 + ((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
      2 * ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3) -
        2 * deriv (g.regularLevelArea hf) b := by
  dsimp only
  intro hind
  have h := D.integral_scalarCurvature_posPart_slab_le_of_scaled_level_induction
    hf hI hproper hreg ha hab hm hα hC hslab hKc hK hsec harea hhess hspeed
    (κ := 1)
  dsimp only at h
  specialize h hind
  have hp : b ^ m ≤ 1 := pow_le_one₀ (ha.trans hab).le hb
  let E := ((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpE := mul_le_mul_of_nonneg_left hp hE
  have hlen : 1 * (b - a) + E * b ^ m ≤ 1 + E := by
    linarith only [ha, hb, hpE]
  have hleft := mul_le_mul_of_nonneg_left hlen
    (show 0 ≤ 2 * α * C by positivity)
  have hright := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 2 * ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3) by positivity)
  dsimp only [E] at hleft
  nlinarith only [h, hleft, hright]

end PoincareConjecture.LeviCivitaData
