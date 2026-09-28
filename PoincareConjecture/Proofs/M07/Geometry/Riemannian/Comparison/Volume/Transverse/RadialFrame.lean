import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Transport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Speed

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem radial_velocity_eq_differential
    {e : EuclideanSpace ℝ (Fin n) → M} (v : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (t • v)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1 =
      mfderiv (𝓡 n) (𝓡 n) e (t • v) v := by
  have hline : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hd := mfderiv_comp t he hline.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun A => A 1) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1 =
    mfderiv (𝓡 n) (𝓡 n) e (t • v) (fderiv ℝ (fun s : ℝ => s • v) t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul, hline.deriv] at hv
  exact hv

theorem chartField_velocity_eq_deriv
    {q : ℝ → M} {a : M} {t : ℝ}
    (hq : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) t =
      deriv ((extChartAt (𝓡 n) a) ∘ q) t := by
  have hd := mfderiv_comp t (mdifferentiableAt_extChartAt
    (by simpa only [extChartAt_source] using ha)) hq
  rw [mfderiv_eq_fderiv] at hd
  exact (congrArg (fun A => A 1) hd).symm

theorem contDiffAt_chartField_velocity
    {q : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) {t : ℝ} (ht : t ∈ I)
    {a : M} (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ (chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)) t := by
  have hqt := hq.contMDiffAt (hI.mem_nhds ht)
  have hrep : (chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)) =ᶠ[𝓝 t]
      deriv ((extChartAt (𝓡 n) a) ∘ q) := by
    filter_upwards [hI.mem_nhds ht, hqt.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds ha)] with s hs hsa
    exact chartField_velocity_eq_deriv
      ((hq.contMDiffAt (hI.mem_nhds hs)).mdifferentiableAt (by simp)) hsa
  exact (((contDiffAt_chart_curve hqt ha).fderiv_right (by simp)).clm_apply
    contDiffAt_const).congr_of_eventuallyEq hrep

theorem IsGeodesicOn.manifoldCovDeriv_velocity_eq_zero
    {g : RiemannianMetric n M} {q : ℝ → M} {I : Set ℝ}
    (hgeo : g.IsGeodesicOn q I) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) {t : ℝ} (ht : t ∈ I) :
    manifoldCovDerivAlong g q (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) 1 t = 0 := by
  have hqt := hq.contMDiffAt (hI.mem_nhds ht)
  let a := q t
  let c := extChartAt (𝓡 n) a
  let U := I ∩ q ⁻¹' c.source
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hI (isOpen_extChartAt_source a)
  have htU : t ∈ U := ⟨ht, mem_extChartAt_source _⟩
  have hgeoU : g.IsGeodesicOn q U := fun s hs => hgeo s hs.1
  have hd := hgeoU.hasDerivAt_in_chart hU a (fun s hs => hs.2) t htU
  have hrep : (chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)) =ᶠ[𝓝 t]
      deriv (c ∘ q) := by
    filter_upwards [hU.mem_nhds htU] with s hs
    exact chartField_velocity_eq_deriv
      ((hq.contMDiffAt (hI.mem_nhds hs.1)).mdifferentiableAt (by simp)) hs.2
  apply (isInvertible_mfderiv_extChartAt (I := 𝓡 n) htU.2).injective
  rw [map_zero, manifoldCovDerivAlong_in_chart g a htU.2 hqt.continuousAt
    ((contDiffAt_chart_curve hqt htU.2).differentiableAt (by simp))
    ((contDiffAt_chartField_velocity hI hq ht htU.2).differentiableAt (by simp))]
  erw [covDerivAlong_congr _ _ hrep]
  change deriv (deriv (c ∘ q)) t +
    CoordinateExponential.christoffelBilinear (g.pullbackCoefficients c.symm)
      (c (q t)) (deriv (c ∘ q) t) (deriv (c ∘ q) t) = 0
  erw [hd.2.deriv]
  exact neg_add_cancel _

theorem parallel_frame_velocity
    (g : RiemannianMetric n M) {q : ℝ → M} {I : Set ℝ} {a b t : ℝ}
    (hab : a < b) (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hsub : Icc a b ⊆ I)
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hPi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hP : ∀ s ∈ Icc a b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q s) (fun r => P r u)) s ∧
      manifoldCovDerivAlong g q (fun r => P r u) 1 s = 0)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : P a v = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q a 1) (ht : t ∈ Icc a b) :
    P t v = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun r => (P r).inverse (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1)) 0 s := by
    have h := inverse_manifold_parallel_hasDerivAt g hab hs hPi
      (hq.contMDiffAt (hI.mem_nhds (hsub hs))) (hP s hs)
      ((contDiffAt_chartField_velocity hI hq (hsub hs) (mem_extChartAt_source _)).differentiableAt
        (by simp))
    rwa [hgeo.manifoldCovDeriv_velocity_eq_zero hI hq (hsub hs), map_zero] at h
  have heq := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (convex_Icc a b) ha ht
  have he : (P t).inverse (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = v := by
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, ← hv,
      (hPi a ha).inverse_apply_self] using heq
  rw [← he, (hPi t ht).self_apply_inverse]

theorem exists_isometric_parallel_frame
    (g : RiemannianMetric n M) {q : ℝ → M} {I : Set ℝ} {a b : ℝ}
    (hab : a < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hsub : Icc a b ⊆ I)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) (q a))
    (hL : ∀ u v, g.inner (q a) (L u) (L v) = inner ℝ u v) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P a = L ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
        manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0) ∧
      ∀ t ∈ Icc a b, ∀ u v, g.inner (q t) (P t u) (P t v) = inner ℝ u v := by
  have hLi : Function.Injective L := by
    intro u v huv
    have h := hL (u - v) (u - v)
    rw [map_sub, huv, sub_self, map_zero] at h
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n))).mp h.symm)
  let e := LinearEquiv.ofBijective L.toLinearMap
    ⟨hLi, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hLi⟩
  have hi : L.IsInvertible := ⟨e.toContinuousLinearEquiv, rfl⟩
  obtain ⟨Q, hQ0, hQi, hQ, hpair⟩ := exists_manifold_parallel_transport g hab hI hq hsub
  refine ⟨fun t => (Q t).comp L, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    change Q a (L u) = L u
    rw [hQ0]
    rfl
  · intro t ht
    exact (hQi t ht).comp hi
  · intro t ht u
    exact hQ t ht (L u)
  · intro t ht u v
    exact (hpair t ht (L u) (L v)).trans (hL u v)

end PoincareConjecture.RiemannianMetric
