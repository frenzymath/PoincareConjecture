import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.ChartAreaDomination

/-!
# Actual supported area approximation in target coordinates

A compact coordinate image has a positive margin inside its target-chart
domain. Choose actual mollifier radii below that margin and use the M40
cutoff blend. The resulting maps remain in the chart, preserve all C1
points, smooth the plateau, and have convergent actual target areas.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal Convolution

namespace PoincareMT.M64Uniformization

open Poincare.Analysis.Sobolev ContinuousLinearMap

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Actual small-radius coordinate mollification stays in the chosen target chart and
preserves outside germs while its true area converges. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-relative-area-approximation.md`. -/
theorem scalar_exists_supported_area_approximation
    (g : RiemannianMetric n M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U)
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {K : Set Plane} (hK : IsCompact K) (huK : MapsTo u K U)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hcompact : HasCompactSupport rho) (hrange : ∀ x, rho x ∈ Icc 0 1) :
    ∃ v : ℕ → Plane → E, ∃ B : ℝ≥0,
      (∀ j, LipschitzWith B (v j)) ∧
      (∀ j, MapsTo (v j) K U) ∧
      (∀ j x, x ∉ tsupport rho → v j =ᶠ[𝓝 x] u) ∧
      (∀ j x, ContDiffAt ℝ 1 u x → ContDiffAt ℝ 1 (v j) x) ∧
      (∀ j x, rho =ᶠ[𝓝 x] 1 → ContDiffAt ℝ ∞ (v j) x) ∧
      TendstoUniformly v u atTop ∧
      (∀ᵐ x ∂volume, ∀ i : Fin 2, Tendsto
        (fun j => fderiv ℝ (v j) x (EuclideanSpace.single i 1)) atTop
        (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1)))) ∧
      Tendsto (fun j => ∫ x in K, m60AreaDensity g (f ∘ v j) x) atTop
        (𝓝 (∫ x in K, m60AreaDensity g (f ∘ u) x)) := by
  have himage : IsCompact (u '' K) := hK.image hu.continuous
  obtain ⟨delta, hdelta, hmargin⟩ := himage.exists_cthickening_subset_open hU
    (by rintro _ ⟨x, hx, rfl⟩; exact huK hx)
  let a : ℝ := min 1 (delta / ((L : ℝ) + 1))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hdelta (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have hadelta : (L : ℝ) * a ≤ delta := by
    calc
      _ ≤ (L : ℝ) * (delta / ((L : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) L.coe_nonneg
      _ ≤ delta := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) + 1)]
        nlinarith
  let r := fun j : ℕ => a * (1 / 2 : ℝ) ^ (j + 1)
  have hr (j : ℕ) : 0 < r j := mul_pos ha (pow_pos (by norm_num) _)
  have hra (j : ℕ) : r j ≤ a := mul_le_of_le_one_right ha.le
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hr1 (j : ℕ) : r j ≤ 1 := (hra j).trans ha1
  have hrd (j : ℕ) : (L : ℝ) * r j ≤ delta :=
    (mul_le_mul_of_nonneg_left (hra j) L.coe_nonneg).trans hadelta
  have hz : Tendsto r atTop (𝓝 0) := by
    simpa only [r, pow_succ, mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)).const_mul a
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hrho (by simp)
  let v := fun j => M40.cutoffBlend rho u (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u)
  let B : ℝ≥0 := L + A * L
  let Q := Metric.cthickening delta (u '' K)
  have hQ : IsCompact Q := himage.cthickening
  have huQ : MapsTo u K Q := fun x hx =>
    Metric.self_subset_cthickening _ (mem_image_of_mem u hx)
  have hvQ (j : ℕ) : MapsTo (v j) K Q := by
    intro x hx
    exact Metric.mem_cthickening_of_dist_le (v j x) (u x) delta (u '' K)
      (mem_image_of_mem u hx)
      ((M40.cutoffBlend_dist_le (hrange x) (scalarVector_mollifier_error hu (hr j) x)).trans
        (hrd j))
  have hv (j : ℕ) : LipschitzWith B (v j) :=
    scalarMollifiedCutoff_lipschitz hu hA hrange (hr j) (hr1 j)
  have hval : TendstoUniformly v u atTop := scalarMollifiedCutoff_uniform hu hrange hr hz
  have hcol : ∀ᵐ x ∂volume, ∀ i : Fin 2, Tendsto
      (fun j => fderiv ℝ (v j) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1))) :=
    scalarMollifiedCutoff_columns_tendsto_ae hu hrho hr hz
  refine ⟨v, B, hv, (fun j _ hx => hmargin (hvQ j hx)),
    (fun j _ hx => scalarMollifiedCutoff_eq_outside u rho (hr j) hx),
    (fun j _ hx => scalarMollifiedCutoff_preserves_C1 hu hrho (hr j) hx),
    (fun j _ hx => scalarMollifiedCutoff_smooth_on_plateau hu (hr j) hx), hval, hcol, ?_⟩
  exact scalarC1_composed_area_integral_tendsto g hU hf hQ hmargin hK
    (hu.weaken (le_add_of_nonneg_right (by positivity))) hv huQ hvQ
    (fun x _ => hval.tendsto_at x) hcol

end PoincareMT.M64Uniformization
