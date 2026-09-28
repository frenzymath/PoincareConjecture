import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.SmoothAction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}

def radiusCoordinate (d : UnitSliceRadialChartData hcomparison n) (c : ℝ)
    (z : ℝ × UnitSliceAmbient n) : UnitSliceAmbient n :=
  d.radialOrbit z.2 (z.1 / c - 1)

theorem radiusCoordinate_center (d : UnitSliceRadialChartData hcomparison n)
    {c : ℝ} (hc : 0 < c) {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    d.radiusCoordinate c (c, x) = x := by
  simp only [radiusCoordinate, div_self hc.ne', sub_self, d.radialOrbit_zero hx]

theorem contDiffAt_radiusCoordinate (d : UnitSliceRadialChartData hcomparison n)
    {c : ℝ} (hc : 0 < c) {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) :
    ContDiffAt ℝ ∞ (d.radiusCoordinate c) (c, x) := by
  have h := d.contDiffAt_radialOrbit_joint_zero hx
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1)
      (c / c - 1, x) := by simpa only [div_self hc.ne', sub_self] using h
  exact ContDiffAt.comp (f := fun z : ℝ × UnitSliceAmbient n => (z.1 / c - 1, z.2))
    (g := fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1) (c, x) hh
    ((contDiffAt_fst.div_const c).sub contDiffAt_const |>.prodMk contDiffAt_snd)

theorem fderiv_radiusCoordinate (d : UnitSliceRadialChartData hcomparison n)
    {c : ℝ} (hc : 0 < c) {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source)
    (a : ℝ) (v : UnitSliceAmbient n) :
    let V : UnitSliceAmbient n := d.connection.gradient d.potential x
    fderiv ℝ (d.radiusCoordinate c) (c, x) (a, v) = (a / c) • V + v := by
  dsimp only
  let A := fun z : ℝ × UnitSliceAmbient n => (z.1 / c - 1, z.2)
  have hA : HasFDerivAt A
      ((c⁻¹ • ContinuousLinearMap.fst ℝ ℝ (UnitSliceAmbient n)).prod
        (ContinuousLinearMap.snd ℝ ℝ (UnitSliceAmbient n))) (c, x) := by
    have hfst : HasFDerivAt (fun z : ℝ × UnitSliceAmbient n => c⁻¹ * z.1 - 1)
        (c⁻¹ • ContinuousLinearMap.fst ℝ ℝ (UnitSliceAmbient n)) (c, x) :=
      (hasFDerivAt_fst.const_mul c⁻¹).sub_const 1
    have hsnd : HasFDerivAt (Prod.snd : ℝ × UnitSliceAmbient n → UnitSliceAmbient n)
        (ContinuousLinearMap.snd ℝ ℝ (UnitSliceAmbient n)) (c, x) := hasFDerivAt_snd
    convert! hfst.prodMk hsnd using 1
    ext z <;> simp only [A, div_eq_mul_inv, mul_comm]
  have hO := ((d.contDiffAt_radialOrbit_joint_zero hx).differentiableAt (by simp)).hasFDerivAt
  have hAvalue : A (c, x) = (0, x) := by simp only [A, div_self hc.ne', sub_self]
  have hO' : HasFDerivAt (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1)
      (fderiv ℝ (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1) (0, x)) (A (c, x)) := by
    rw [hAvalue]
    exact hO
  have hh := congrArg (fun B : (ℝ × UnitSliceAmbient n) →L[ℝ] UnitSliceAmbient n => B (a, v))
    (hO'.comp (c, x) hA).fderiv
  change fderiv ℝ (d.radiusCoordinate c) (c, x) (a, v) = _ at hh
  rw [hh]
  change fderiv ℝ (fun z : ℝ × UnitSliceAmbient n => d.radialOrbit z.2 z.1) (0, x)
    (c⁻¹ * a, v) = _
  rw [mul_comm, ← div_eq_mul_inv]
  exact d.fderiv_radialOrbit_joint_zero hx (a / c) v

theorem inner_radiusCoordinate_of_level_tangent
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c)
    {x : UnitSliceAmbient n} (hx : x ∈ d.ambientChart.source) (hlevel : d.potential x = 1 / 2)
    (a b : ℝ) (v w : UnitSliceAmbient n)
    (hv : fderiv ℝ d.potential x v = 0) (hw : fderiv ℝ d.potential x w = 0) :
    (d.dilate c hc).metric.inner x
      (fderiv ℝ (d.radiusCoordinate c) ((c : ℝ), x) (a, v))
      (fderiv ℝ (d.radiusCoordinate c) ((c : ℝ), x) (b, w)) =
        a * b + (c : ℝ) ^ 2 * d.metric.inner x v w := by
  have hc' : 0 < (c : ℝ) := hc
  have hgrad : d.metric.inner x (d.connection.gradient d.potential x)
      (d.connection.gradient d.potential x) = 1 := by
    have hh := d.eikonal x hx
    rw [hlevel] at hh
    norm_num only [mul_one_div_cancel] at hh
    exact hh
  have horth (u : UnitSliceAmbient n) (hu : fderiv ℝ d.potential x u = 0) :
      d.metric.inner x (d.connection.gradient d.potential x) u = 0 := by
    rw [d.connection.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    exact hu
  rw [d.dilate_inner, d.fderiv_radiusCoordinate hc' hx, d.fderiv_radiusCoordinate hc' hx]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [hgrad, horth w hw, d.metric.symm x v (d.connection.gradient d.potential x), horth v hv]
  field_simp
  ring

theorem inner_radiusCoordinate_regularLevel
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c)
    (z : d.Level) (a b : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    letI : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    let ι := openLevelIncl d.potential d.source (1 / 2)
    (d.dilate c hc).metric.inner (ι z)
      (fderiv ℝ (d.radiusCoordinate c) ((c : ℝ), ι z) (a, mfderiv (𝓡 n) (𝓡 (n + 1)) ι z v))
      (fderiv ℝ (d.radiusCoordinate c) ((c : ℝ), ι z) (b, mfderiv (𝓡 n) (𝓡 (n + 1)) ι z w)) =
        a * b + (c : ℝ) ^ 2 *
          (RiemannianMetric.regularLevelMetric d.smooth d.source d.regular (1 / 2) d.metric).inner z v w := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  dsimp only
  have hker (u : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ d.potential (openLevelIncl d.potential d.source (1 / 2) z)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl d.potential d.source (1 / 2)) z u) = 0 := by
    have hmem := LinearMap.mem_range_self
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl d.potential d.source (1 / 2)) z).toLinearMap u
    rw [range_mfderiv_openLevelIncl d.smooth d.source d.regular n (1 / 2) z] at hmem
    change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) d.potential
      (openLevelIncl d.potential d.source (1 / 2) z)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl d.potential d.source (1 / 2)) z u) = 0 at hmem
    rw [mfderiv_eq_fderiv] at hmem
    exact hmem
  exact d.inner_radiusCoordinate_of_level_tangent c hc z.1.2 z.2 a b _ _ (hker v) (hker w)

def polarMap (d : UnitSliceRadialChartData hcomparison n) (c : ℝ)
    (q : ℝ × d.Level) : UnitSliceAmbient n :=
  d.radiusCoordinate c (q.1, openLevelIncl d.potential d.source (1 / 2) q.2)

theorem contMDiffAt_polarMap (d : UnitSliceRadialChartData hcomparison n)
    {c : ℝ} (hc : 0 < c) (z : d.Level) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (d.polarMap c) (c, z) := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hι : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (openLevelIncl d.potential d.source (1 / 2)) :=
    contMDiff_openLevelIncl d.smooth d.source d.regular n (1 / 2)
  have hcoords : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, ℝ × UnitSliceAmbient n) ∞
      (fun q : ℝ × d.Level => (q.1, openLevelIncl d.potential d.source (1 / 2) q.2)) (c, z) :=
    contMDiffAt_fst.prodMk_space (ContMDiffAt.comp
      (f := (Prod.snd : ℝ × d.Level → d.Level))
      (g := openLevelIncl d.potential d.source (1 / 2)) (c, z) (hι z) contMDiffAt_snd)
  have hradial := contMDiffAt_iff_contDiffAt.mpr (d.contDiffAt_radiusCoordinate hc z.1.2)
  exact hradial.comp (c, z) hcoords

theorem mfderiv_polarMap (d : UnitSliceRadialChartData hcomparison n)
    {c : ℝ} (hc : 0 < c) (z : d.Level) (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) (c, z) (a, v) =
      fderiv ℝ (d.radiusCoordinate c) (c, openLevelIncl d.potential d.source (1 / 2) z)
        (a, mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl d.potential d.source (1 / 2)) z v) := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let ι := openLevelIncl d.potential d.source (1 / 2)
  have hι : MDifferentiableAt (𝓡 n) (𝓡 (n + 1)) ι z :=
    (contMDiff_openLevelIncl d.smooth d.source d.regular n (1 / 2) z).mdifferentiableAt (by simp)
  have hcoords : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (Prod.map id ι) (c, z) :=
    mdifferentiableAt_id.prodMap hι
  have hr : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1))
      (d.radiusCoordinate c) (c, ι z) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contMDiffAt_iff_contDiffAt.mpr
      (d.contDiffAt_radiusCoordinate hc z.1.2)).mdifferentiableAt (by simp)
  have hderiv := mfderiv_comp (c, z) hr hcoords
  rw [mfderiv_prodMap mdifferentiableAt_id hι, mfderiv_id] at hderiv
  have hh := congrArg (fun A => A (a, v)) hderiv
  change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) (c, z) (a, v) =
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) (d.radiusCoordinate c) (c, ι z)
      (a, mfderiv (𝓡 n) (𝓡 (n + 1)) ι z v) at hh
  have hradialD : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1))
      (d.radiusCoordinate c) (c, ι z) = fderiv ℝ (d.radiusCoordinate c) (c, ι z) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv]
  erw [hradialD] at hh
  exact hh

theorem inner_polarMap (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) (z : d.Level) (a b : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    letI : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    (d.dilate c hc).metric.inner (d.polarMap c ((c : ℝ), z))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((c : ℝ), z) (a, v))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((c : ℝ), z) (b, w)) =
        a * b + (c : ℝ) ^ 2 *
          (RiemannianMetric.regularLevelMetric d.smooth d.source d.regular (1 / 2) d.metric).inner z v w := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hcenter : d.polarMap c ((c : ℝ), z) = openLevelIncl d.potential d.source (1 / 2) z :=
    d.radiusCoordinate_center hc z.1.2
  erw [d.mfderiv_polarMap hc, d.mfderiv_polarMap hc]
  erw [hcenter]
  exact d.inner_radiusCoordinate_regularLevel c hc z a b v w

theorem isInvertible_mfderiv_polarMap (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) (z : d.Level) :
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((c : ℝ), z)).IsInvertible := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let g := RiemannianMetric.regularLevelMetric d.smooth d.source d.regular (1 / 2) d.metric
  let A : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] UnitSliceAmbient n :=
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((c : ℝ), z)
  have hi : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨a, v⟩ hav
    have hnorm := d.inner_polarMap c hc z a a v v
    change (d.dilate c hc).metric.inner (d.polarMap c ((c : ℝ), z))
      (A (a, v)) (A (a, v)) = a * a + (c : ℝ) ^ 2 * g.inner z v v at hnorm
    erw [hav] at hnorm
    simp only [map_zero] at hnorm
    have hnonneg : 0 ≤ g.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos z v hv).le
    have hv : v = 0 := by
      by_contra hne
      have hp := mul_pos (show 0 < (c : ℝ) ^ 2 by positivity) (g.pos z v hne)
      nlinarith [sq_nonneg a]
    have ha : a = 0 := by
      rw [hv] at hnorm
      simp only [map_zero, mul_zero, add_zero] at hnorm
      nlinarith [sq_nonneg a]
    simp [ha, hv]
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (UnitSliceAmbient n) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, Nat.add_comm]
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
