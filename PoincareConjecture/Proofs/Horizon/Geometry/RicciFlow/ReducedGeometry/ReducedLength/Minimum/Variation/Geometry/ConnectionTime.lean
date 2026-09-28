import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.AdaptedCoefficient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.CoefficientRegularity















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local instance connectionTimeEndGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance connectionTimeEndSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance connectionTimeBilinearGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance connectionTimeBilinearSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace



theorem connection_time_deriv_eq_extend
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {y : M}
    {Y : (z : M) → TangentSpace (𝓡 n) z}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) y) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    deriv (fun r => (F.connection r).connection Y y) t =
      deriv (fun r => (F.connection r).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y y)) y) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y y)
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (k := ∞) (Y y)
  have heq (r : ℝ) :
      (F.connection r).connection Y y - (F.connection t).connection Y y =
        (F.connection r).connection Z y - (F.connection t).connection Z y := by
    have h₁ := (F.connection r).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp)
      (hY.mdifferentiableAt (by simp))
    have h₂ := (F.connection r).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp)
      (hZ.mdifferentiableAt (by simp))
    simp only [FiberBundle.extend_apply_self] at h₂
    exact h₁.symm.trans h₂
  have h₁ := ((F.contDiffAt_connection ht hY).differentiableAt (by simp)).hasDerivAt.sub_const
    ((F.connection t).connection Y y)
  have h₂ := ((F.contDiffAt_connection ht hZ).differentiableAt (by simp)).hasDerivAt.sub_const
    ((F.connection t).connection Z y)
  exact h₁.unique (h₂.congr_of_eventuallyEq (Eventually.of_forall heq))



theorem connection_time_deriv_pairing
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {y : M}
    {Y : (z : M) → TangentSpace (𝓡 n) z}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) y)
    (v w : TangentSpace (𝓡 n) y) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.metric t).inner y ((deriv (fun r => (F.connection r).connection Y y) t) v) w =
      -backwardConnectionVariationPairing (F.connection t) y v (Y y) w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  rw [connection_time_deriv_eq_extend F ht hY,
    F.inner_deriv_connection_extend_of_equation ht]
  unfold backwardConnectionVariationPairing ricciDerivativePairing
  ring



theorem squareTime_connection_deriv_pairing
    {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) {s : ℝ}
    (ht : T - s ^ 2 ∈ interior J) {y : M}
    {Y : (z : M) → TangentSpace (𝓡 n) z}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) y)
    (v w : TangentSpace (𝓡 n) y) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    (F.metric (T - s ^ 2)).inner y
        (deriv (fun r => (F.connection (T - r ^ 2)).connection Y y v) s) w =
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) y v (Y y) w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  have hC := ((F.contDiffAt_connection ht hY).differentiableAt (by simp)).hasDerivAt
  have hCv := hC.clm_apply (hasDerivAt_const (T - s ^ 2) v)
  have htime : HasDerivAt (fun r : ℝ => T - r ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub T
  have hd := (hCv.scomp s htime).deriv
  simp only [Function.comp_def, map_zero, add_zero] at hd
  rw [hd]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [connection_time_deriv_pairing F ht hY]
  ring



theorem chartConnectionBilinear_time_pairing
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (fderiv ℝ (chartConnectionBilinear (chartActionMetric F T x))
          (s, extChartAt (𝓡 n) x y) (1, 0) v w) z =
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by
    simpa only [extChartAt_source] using hy
  have hq : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨squareTime_mem_interior_preimage ht, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hC := ((chartConnectionBilinear_contDiffOn (chartActionMetric F T x)
    (chartActionDomain F T x) (chartActionDomain_open F T x)
    (chartActionMetric_contDiffOn F T x)
    (fun z hz => chartActionMetric_pos F T x hz)) _ hq).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hq)
  have hc := (hC.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s (extChartAt (𝓡 n) x y)))
  have hvw := (hc.clm_apply (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s w)
  simp only [Function.comp_def, map_zero, add_zero] at hvw
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hframe := (e.symmL ℝ y).hasFDerivAt.comp_hasDerivAt s hvw
  have heq : (fun r => (F.connection (T - r ^ 2)).connection
      (chartFrame x w) y (chartFrame x v y)) =ᶠ[𝓝 s]
      fun r => e.symmL ℝ y
        (chartConnectionBilinear (chartActionMetric F T x)
          (r, extChartAt (𝓡 n) x y) v w) := by
    filter_upwards [(continuous_const.sub (continuous_id.pow 2)).continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds ht)] with r hr
    exact chartConnection_eq_retainedConnection F T r x y hy hr v w
  have hd := (hframe.congr_of_eventuallyEq heq).deriv
  have hY := (chartFrame_contMDiffOn x w y hy).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)
  rw [chartActionMetric_apply F T hy]
  change (F.metric (T - s ^ 2)).inner y
    (e.symmL ℝ y (fderiv ℝ (chartConnectionBilinear (chartActionMetric F T x))
      (s, extChartAt (𝓡 n) x y) (1, 0) v w)) (chartFrame x z y) = _
  rw [← hd]
  exact squareTime_connection_deriv_pairing F T ht hY (chartFrame x v y) (chartFrame x z y)

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
