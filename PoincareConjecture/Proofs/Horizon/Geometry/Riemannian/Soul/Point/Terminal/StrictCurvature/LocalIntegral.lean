import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.RadialJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialGauss
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Conjugate

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T2Space M] in


theorem inner_parallel_eq_endpoint
    {q : ℝ → M} {V W : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (chartField q (q t) V) t)
    (hW : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (chartField q (q t) W) t)
    (hDV : ∀ t ∈ Icc (0 : ℝ) 1, manifoldCovDerivAlong g q V 1 t = 0)
    (hDW : ∀ t ∈ Icc (0 : ℝ) 1, manifoldCovDerivAlong g q W 1 t = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g.inner (q t) (V t) (W t) = g.inner (q 1) (V 1) (W 1) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => g.inner (q r) (V r) (W r)) 0 s := by
    have h := hasDerivAt_metric_inner_along g (hq s hs) (hV s hs) (hW s hs)
    simpa [hDV s hs, hDW s hs] using h
  have hc := constant_of_derivWithin_zero
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one s ⟨hs.1, hs.2.le⟩))
  exact (hc t ht).trans (hc 1 ⟨zero_le_one, le_rfl⟩).symm



theorem gram_affine_parallel_geodesic
    {q : ℝ → M} {I : Set ℝ} {Z : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    {C : ℝ} (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I)
    (hsub : Icc (0 : ℝ) 1 ⊆ I)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (chartField q (q t) Z) t)
    (hDZ : ∀ t ∈ Icc (0 : ℝ) 1, manifoldCovDerivAlong g q Z 1 t = 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g.inner (q t) (t • Z t) (t • Z t) *
        g.inner (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) -
      (g.inner (q t) (t • Z t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) ^ 2 =
      t ^ 2 * (C ^ 2 * g.tangentNorm (q 1) (Z 1) ^ 2 -
        (g.inner (q 1) (Z 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let T : (s : ℝ) → TangentSpace (𝓡 n) (q s) :=
    fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I :=
    fun s hs => (Realization.contMDiffAt_of_isGeodesicOn hgeo hs).contMDiffWithinAt
  have hqt (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q s :=
    hq.contMDiffAt (hI.mem_nhds (hsub hs))
  have hT s (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (chartField q (q s) T) s :=
    RiemannianMetric.contDiffAt_chartField_velocity_at (hqt s hs) (mem_extChartAt_source _)
  have hDT s (hs : s ∈ Icc (0 : ℝ) 1) : manifoldCovDerivAlong g q T 1 s = 0 :=
    hgeo.manifoldCovDerivAlong_velocity_eq_zero hI hq (hsub hs)
  have hZZ := inner_parallel_eq_endpoint hqt hZ hZ hDZ hDZ ht
  have hZT := inner_parallel_eq_endpoint hqt hZ hT hDZ hDT ht
  have hsq (s : ℝ) (v : TangentSpace (𝓡 n) (q s)) :
      g.tangentNorm (q s) v ^ 2 = g.inner (q s) v v :=
    Real.sq_sqrt (show 0 ≤ inner ℝ v v from real_inner_self_nonneg)
  have hTT : g.inner (q t) (T t) (T t) = C ^ 2 := by
    rw [← hsq, hspeed t ht]
  have hscale : g.inner (q t) (t • Z t) (t • Z t) * g.inner (q t) (T t) (T t) -
      (g.inner (q t) (t • Z t) (T t)) ^ 2 =
      t ^ 2 * (g.inner (q t) (Z t) (Z t) * g.inner (q t) (T t) (T t) -
        (g.inner (q t) (Z t) (T t)) ^ 2) := by
    change inner ℝ (t • Z t) (t • Z t) * inner ℝ (T t) (T t) -
      (inner ℝ (t • Z t) (T t)) ^ 2 =
      t ^ 2 * (inner ℝ (Z t) (Z t) * inner ℝ (T t) (T t) -
        (inner ℝ (Z t) (T t)) ^ 2)
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring
  change g.inner (q t) (t • Z t) (t • Z t) * g.inner (q t) (T t) (T t) -
    (g.inner (q t) (t • Z t) (T t)) ^ 2 = _
  rw [hscale, hZZ, hTT, hZT, ← hsq 1 (Z 1)]
  ring



theorem curvature_integral_lower_bound_of_parallel
    (D : LeviCivitaData g)
    {q : ℝ → M} {I : Set ℝ} {Z : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    {C κ s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I) (hsub : Icc (0 : ℝ) 1 ⊆ I)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (chartField q (q t) Z) t)
    (hDZ : ∀ t ∈ Icc (0 : ℝ) 1, manifoldCovDerivAlong g q Z 1 t = 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hcontinuous : ContinuousOn (fun t => D.curvatureTensor (q t) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) (Icc 0 1))
    (hsec : D.NonnegativeSectionalCurvature)
    (hlower : ∀ t ∈ Icc s 1, ∀ u v : TangentSpace (𝓡 n) (q t),
      g.inner (q t) u u = 1 → g.inner (q t) v v = 1 →
      g.inner (q t) u v = 0 → κ ≤ D.sectionalCurvature (q t) u v) :
    κ * (C ^ 2 * g.tangentNorm (q 1) (Z 1) ^ 2 -
        (g.inner (q 1) (Z 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) ^ 2) *
        ((1 - s ^ 3) / 3) ≤
      ∫ t in (0 : ℝ)..1, D.curvatureTensor (q t) (t • Z t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
  let F := fun t => D.curvatureTensor (q t) (t • Z t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
  let A := κ * (C ^ 2 * g.tangentNorm (q 1) (Z 1) ^ 2 -
    (g.inner (q 1) (Z 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) ^ 2)
  have hFs : ContinuousOn F (Icc s 1) :=
    hcontinuous.mono (Icc_subset_Icc hs.1 le_rfl)
  have hFi : IntervalIntegrable F volume 0 1 :=
    hcontinuous.intervalIntegrable_of_Icc zero_le_one
  have hbound (t : ℝ) (ht : t ∈ Icc s 1) : A * t ^ 2 ≤ F t := by
    have h := D.curvatureTensor_diagonal_lower_bound_of_orthonormal (q t)
      (hlower t ht) (t • Z t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
    rw [gram_affine_parallel_geodesic hI hgeo hsub hZ hDZ hspeed
      ⟨hs.1.trans ht.1, ht.2⟩] at h
    convert h using 1
    dsimp [A, F]
    ring
  have hmono : (∫ t in s..1, A * t ^ 2) ≤ ∫ t in s..1, F t :=
    intervalIntegral.integral_mono_on hs.2
      ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable s 1)
      (hFs.intervalIntegrable_of_Icc hs.2) hbound
  have hfull : (∫ t in s..1, F t) ≤ ∫ t in (0 : ℝ)..1, F t :=
    intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      (Eventually.of_forall fun t => hsec (q t) (t • Z t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) hFi
  have hpoly : (∫ t in s..1, A * t ^ 2) = A * ((1 - s ^ 3) / 3) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hpoly] at hmono
  exact hmono.trans hfull



theorem jacobi_inner_le_sub_local_curvature_of_minimizing
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b C κ s : ℝ}
    (ha : a < 0) (hb : 1 < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ0 : J 0 = 0) (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hmin : g.edist (q 0) (q 1) = ENNReal.ofReal C)
    (hsec : D.NonnegativeSectionalCurvature)
    (hlower : ∀ t ∈ Icc s 1, ∀ u v : TangentSpace (𝓡 n) (q t),
      g.inner (q t) u u = 1 → g.inner (q t) v v = 1 →
      g.inner (q t) u v = 0 → κ ≤ D.sectionalCurvature (q t) u v) :
    g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) ≤
      g.inner (q 1) (J 1) (J 1) -
        κ * (C ^ 2 * g.tangentNorm (q 1) (J 1) ^ 2 -
          (g.inner (q 1) (J 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) ^ 2) *
          ((1 - s ^ 3) / 3) := by
  obtain ⟨Z, hZ, hDZ, hZ1, _, hcontinuous, hbound⟩ :=
    exists_parallel_field_jacobi_inner_le_sub_curvature_integral_of_minimizing
      D ha hb hI hgeo hsub hJ hjac hJ0 hC hspeed hmin
  have h01 : Icc (0 : ℝ) 1 ⊆ Icc a b :=
    Icc_subset_Icc ha.le hb.le
  have hquant := curvature_integral_lower_bound_of_parallel D hs hI hgeo
    (h01.trans hsub) (fun t ht => hZ t (h01 ht)) (fun t ht => hDZ t (h01 ht))
    hspeed hcontinuous hsec hlower
  rw [hZ1] at hquant
  exact hbound.trans (sub_le_sub_left hquant _)

end PoincareConjecture.Conjugate
