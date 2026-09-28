import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.SweptAnnulus
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.RadialAffineArea
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.AreaDensityProduct
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ScalarFactorArea













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture



def m64SweepOpen (a b : ℝ) : Set LoopPlane :=
  {p | 0 < p 0 ∧ p 0 < curvePeriod ∧ a < p 1 ∧ p 1 < b}



theorem isOpen_m64SweepOpen (a b : ℝ) : IsOpen (m64SweepOpen a b) := by
  have h0 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact (isOpen_lt continuous_const h0).inter
    ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))



theorem m64SweepTime_mem_interior {a b s t u : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hne : s ≠ t)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    s + (t - s) * u ∈ Ioo a b := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hlow := mul_pos (sub_pos.mpr hst) hu.1
    have hhigh := mul_pos (sub_pos.mpr hst) (sub_pos.mpr hu.2)
    constructor <;> nlinarith [hs.1, ht.2]
  · have hlow := mul_pos (sub_pos.mpr hts) (sub_pos.mpr hu.2)
    have hhigh := mul_pos (sub_pos.mpr hts) hu.1
    constructor <;> nlinarith [ht.1, hs.2]

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}




theorem m64_c2_spacetime_lipschitz
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hvelocity : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (curveVelocity (fun y => c y u) x) ≤ S)
    (hcurvature : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (m62CurvatureVector F c u x) ≤ H) :
    ∀ p ∈ m64SweepOpen a b, ∀ q ∈ m64SweepOpen a b,
      g.edist (c (p 0) (p 1)) (c (q 0) (q 1)) ≤
        ENNReal.ofReal (S + H) * ENNReal.ofReal ‖p - q‖ := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro p hp q hq
  have hpx : p 0 ∈ Icc 0 curvePeriod := ⟨hp.1.le, hp.2.1.le⟩
  have hqx : q 0 ∈ Icc 0 curvePeriod := ⟨hq.1.le, hq.2.1.le⟩
  have hpt : p 1 ∈ Icc a b := ⟨hp.2.2.1.le, hp.2.2.2.le⟩
  have hqt : q 1 ∈ Icc a b := ⟨hq.2.2.1.le, hq.2.2.2.le⟩
  have hcoord (i : Fin 2) : |p i - q i| ≤ ‖p - q‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) i
  calc
    _ ≤ g.edist (c (p 0) (p 1)) (c (q 0) (p 1)) +
        g.edist (c (q 0) (p 1)) (c (q 0) (q 1)) := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal |p 0 - q 0| +
        ENNReal.ofReal H * ENNReal.ofReal |p 1 - q 1| :=
      add_le_add (m64_c2_spatial_slice_edist hc g hpt hS
        (fun x hx => hvelocity x hx _ hpt) hpx hqx)
        (m64_c2_time_slice_edist hc g hH (hcurvature _ hqx) hpt hqt)
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal ‖p - q‖ +
        ENNReal.ofReal H * ENNReal.ofReal ‖p - q‖ := by
      gcongr <;> exact hcoord _
    _ = _ := by rw [ENNReal.ofReal_add hS hH, add_mul]




theorem m64SweptMap_density_bound
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hvelocity : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (curveVelocity (fun y => c y u) x) ≤ S)
    (hcurvature : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (m62CurvatureVector F c u x) ≤ H)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) :
    m60AreaDensity g (m64SweptMap c s t) p ≤ (2 * (S + H)) ^ 2 * |t - s| := by
  have hp0 : p 0 ∈ Ioo 0 curvePeriod := hp 0 (mem_univ _)
  have hp1 : p 1 ∈ Ioo (0 : ℝ) 1 := hp 1 (mem_univ _)
  by_cases hst : s = t
  · subst t
    have hzero : m60AreaDensity g (m64SweptMap c s s) p = 0 := by
      apply m60AreaDensity_eq_zero_of_scalar_increment_bound g
        (ell := fun q : LoopPlane => q 0) (K := ⟨S, hS⟩)
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).differentiableAt
      have hneighborhood := (isOpen_Ioo.preimage
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).mem_nhds hp0
      filter_upwards [hneighborhood] with q hq
      simp only [m64SweptMap, m64SweepTime, sub_self, zero_mul, add_zero,
        ENNReal.coe_nnreal_eq]
      exact m64_c2_spatial_slice_edist hc g hs hS
        (fun x hx => hvelocity x hx s hs) ⟨hq.1.le, hq.2.le⟩ ⟨hp0.1.le, hp0.2.le⟩
    simp [hzero]
  · have hne : t - s ≠ 0 := sub_ne_zero.mpr (fun he => hst he.symm)
    let f : LoopPlane → M := fun q => c (q 0) (q 1)
    have hgerm : m64SweptMap c s t =ᶠ[𝓝 p] f ∘ m64RadialAffine (t - s) s := by
      have hneighborhood := (isOpen_Ioo.preimage
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).mem_nhds hp1
      filter_upwards [hneighborhood] with q hq
      dsimp only [m64SweptMap, Function.comp_def, f, m64RadialAffine, annulusPoint]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [m64SweepTime_eq_of_mem ⟨hq.1.le, hq.2.le⟩]
      congr 1
      ring
    have hmem : m64RadialAffine (t - s) s p ∈ m64SweepOpen a b := by
      have htime := m64SweepTime_mem_interior hs ht hst hp1
      change 0 < p 0 ∧ p 0 < curvePeriod ∧
        a < (t - s) * p 1 + s ∧ (t - s) * p 1 + s < b
      exact ⟨hp0.1, hp0.2, by linarith [htime.1], by linarith [htime.2]⟩
    rw [m60AreaDensity_congr_of_eventuallyEq g hgerm,
      m64AreaDensity_comp_radialAffine g f hne s]
    calc
      _ ≤ |t - s| * (2 * (S + H)) ^ 2 := mul_le_mul_of_nonneg_left
        (m60AreaDensity_le_of_metric_lipschitzOn g (isOpen_m64SweepOpen a b)
          (add_nonneg hS hH) (m64_c2_spacetime_lipschitz hc g hS hH hvelocity hcurvature)
          hmem) (abs_nonneg _)
      _ = _ := mul_comm _ _



theorem m64Annulus_of_c2_sweep_area
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ∃ A : M64Annulus g (fun x => c x s) (fun x => c x t),
        A.map = m64SweptMap c s t ∧ A.area ≤ C * |t - s| := by
  obtain ⟨S, H, hS, hH, hvelocity, hcurvature⟩ := m64_c2_sweep_fixed_metric_bounds hc g
  refine ⟨(2 * (S + H)) ^ 2 * volume.real m64AnnulusDomain,
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg, ?_⟩
  intro s hs t ht
  obtain ⟨A, hmap⟩ := m64Annulus_of_c2_sweep hc g hs ht
  refine ⟨A, hmap, ?_⟩
  have hbound : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaDensity g A.map p ≤ (2 * (S + H)) ^ 2 * |t - s| := by
    apply (ae_restrict_iff' m64AnnulusDomain_measurableSet).mpr
    filter_upwards [m64AnnulusDomain_ae_eq_interior] with p hp hpd
    rw [hmap]
    exact m64SweptMap_density_bound hc g hS hH hvelocity hcurvature hs ht (hp.mp hpd)
  have h := m64AnnulusIntegral_le_of_ae_density_bound
    m64AnnulusDomain_volume_ne_top A.area_integrable hbound
  change (∫ p in m64AnnulusDomain, m60AreaDensity g A.map p) ≤ _
  convert h using 1
  ring

end PoincareConjecture
