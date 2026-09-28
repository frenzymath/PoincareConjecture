import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.C2Bounds













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture




noncomputable def m64SweepTime (s t u : ℝ) : ℝ :=
  s + (t - s) * max 0 (min 1 u)



theorem m64SweepTime_eq_of_mem {s t u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    m64SweepTime s t u = s + (t - s) * u := by
  simp only [m64SweepTime, min_eq_right hu.2, max_eq_right hu.1]



theorem m64SweepTime_mem {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (u : ℝ) :
    m64SweepTime s t u ∈ Icc a b := by
  let v := max 0 (min 1 u)
  have hv0 : 0 ≤ v := le_max_left _ _
  have hv1 : v ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hv : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have heq : m64SweepTime s t u = (1 - v) * s + v * t := by
    dsimp [m64SweepTime, v]
    ring
  rw [heq]
  constructor
  · calc
      a = (1 - v) * a + v * a := by ring
      _ ≤ (1 - v) * s + v * t := add_le_add
        (mul_le_mul_of_nonneg_left hs.1 hv) (mul_le_mul_of_nonneg_left ht.1 hv0)
  · calc
      _ ≤ (1 - v) * b + v * b := add_le_add
        (mul_le_mul_of_nonneg_left hs.2 hv) (mul_le_mul_of_nonneg_left ht.2 hv0)
      _ = b := by ring



noncomputable def m64SweptMap {M : Type u} (c : ℝ → ℝ → M) (s t : ℝ)
    (p : LoopPlane) : M := c (p 0) (m64SweepTime s t (p 1))

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}



theorem m64SweptMap_lipschitz
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hvelocity : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (curveVelocity (fun y => c y u) x) ≤ S)
    (hcurvature : ∀ x ∈ Icc 0 curvePeriod, ∀ u ∈ Icc a b,
      g.tangentNorm (c x u) (m62CurvatureVector F c u x) ≤ H)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∀ p q : m64AnnulusDomain,
      g.edist (m64SweptMap c s t p) (m64SweptMap c s t q) ≤
        ENNReal.ofReal (S + H * |t - s|) * ENNReal.ofReal ‖(p : LoopPlane) - q‖ := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro p q
  let up := m64SweepTime s t ((p : LoopPlane) 1)
  let uq := m64SweepTime s t ((q : LoopPlane) 1)
  have hup : up ∈ Icc a b := m64SweepTime_mem hs ht _
  have huq : uq ∈ Icc a b := m64SweepTime_mem hs ht _
  have hp : (p : LoopPlane) 0 ∈ Icc 0 curvePeriod := ⟨p.property.1, p.property.2.1⟩
  have hq : (q : LoopPlane) 0 ∈ Icc 0 curvePeriod := ⟨q.property.1, q.property.2.1⟩
  have hcoord (i : Fin 2) : |(p : LoopPlane) i - (q : LoopPlane) i| ≤
      ‖(p : LoopPlane) - q‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((p : LoopPlane) - (q : LoopPlane)) i
  have htime : |up - uq| ≤ |t - s| * ‖(p : LoopPlane) - q‖ := by
    dsimp only [up, uq]
    rw [m64SweepTime_eq_of_mem ⟨p.property.2.2.1, p.property.2.2.2⟩,
      m64SweepTime_eq_of_mem ⟨q.property.2.2.1, q.property.2.2.2⟩,
      show s + (t - s) * (p : LoopPlane) 1 - (s + (t - s) * (q : LoopPlane) 1) =
        (t - s) * ((p : LoopPlane) 1 - (q : LoopPlane) 1) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left (hcoord 1) (abs_nonneg _)
  have hspatial := m64_c2_spatial_slice_edist hc g hup hS
    (fun x hx => hvelocity x hx up hup) hp hq
  have htemporal := m64_c2_time_slice_edist hc g hH (hcurvature _ hq) hup huq
  calc
    _ ≤ g.edist (c ((p : LoopPlane) 0) up) (c ((q : LoopPlane) 0) up) +
        g.edist (c ((q : LoopPlane) 0) up) (c ((q : LoopPlane) 0) uq) :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal |(p : LoopPlane) 0 - (q : LoopPlane) 0| +
        ENNReal.ofReal H * ENNReal.ofReal |up - uq| := add_le_add hspatial htemporal
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal ‖(p : LoopPlane) - q‖ +
        ENNReal.ofReal H * ENNReal.ofReal (|t - s| * ‖(p : LoopPlane) - q‖) := by
      gcongr
      exact hcoord 0
    _ = _ := by
      rw [ENNReal.ofReal_add hS (mul_nonneg hH (abs_nonneg _)),
        ENNReal.ofReal_mul hH, ENNReal.ofReal_mul (abs_nonneg _)]
      ring



theorem m64Annulus_of_c2_sweep
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ A : M64Annulus g (fun x => c x s) (fun x => c x t),
      A.map = m64SweptMap c s t := by
  obtain ⟨S, H, hS, hH, hvelocity, hcurvature⟩ := m64_c2_sweep_fixed_metric_bounds hc g
  have htime : Continuous (fun p : LoopPlane => m64SweepTime s t (p 1)) := by
    unfold m64SweepTime
    fun_prop
  have hcontinuous : ContinuousOn (m64SweptMap c s t) m64AnnulusDomain := by
    apply hc.continuous.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk htime).continuousOn
    intro p _
    exact ⟨mem_univ _, m64SweepTime_mem hs ht _⟩
  have hperiodic : ∀ x u : ℝ,
      m64SweptMap c s t (annulusPoint (x + curvePeriod) u) =
        m64SweptMap c s t (annulusPoint x u) := by
    intro x u
    exact hc.periodic _ (m64SweepTime_mem hs ht u) x
  have hlower (x : ℝ) : m64SweptMap c s t (annulusPoint x 0) = c x s := by
    simp [m64SweptMap, annulusPoint, m64SweepTime]
  have hupper (x : ℝ) : m64SweptMap c s t (annulusPoint x 1) = c x t := by
    simp [m64SweptMap, annulusPoint, m64SweepTime]
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨A, hmap, _⟩ := m64Annulus_of_lipschitz g _ hcontinuous hperiodic hlower hupper
    (add_nonneg hS (mul_nonneg hH (abs_nonneg _)))
    (m64SweptMap_lipschitz hc g hS hH hvelocity hcurvature hs ht) hfinite
    (show m64AnnulusArea g (m64SweptMap c s t) <
      m64AnnulusArea g (m64SweptMap c s t) + 1 by linarith)
  exact ⟨A, hmap⟩

end PoincareConjecture
