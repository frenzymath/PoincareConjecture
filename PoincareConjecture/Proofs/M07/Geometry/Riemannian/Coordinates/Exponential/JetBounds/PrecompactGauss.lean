import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CovariantPullback








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation ConnectionAlongCurve

private theorem hasDerivAt_coordinate_variation_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q : ℝ × ℝ → E} {t K : ℝ}
    (hq : ContDiffAt ℝ ∞ q (t, 0))
    (hB : DifferentiableAt ℝ B (q (t, 0)))
    (hinv : (B (q (t, 0))).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (q (t, 0)), ∀ u v, B y u v = B y v u)
    (hgeo : HasDerivAt (fun r => deriv (fun z => q (z, 0)) r)
      (-coordinateChristoffel B (q (t, 0))
        (deriv (fun z => q (z, 0)) t) (deriv (fun z => q (z, 0)) t)) t)
    (henergy : HasDerivAt
      (fun s => B (q (t, s)) (deriv (fun r => q (r, s)) t)
        (deriv (fun r => q (r, s)) t)) (2 * K) 0) :
    HasDerivAt
      (fun r => B (q (r, 0)) (deriv (fun z => q (z, 0)) r)
        (fderiv ℝ (fun s => q (r, s)) 0 1)) K t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let Z : ℝ → E := fun s => fderiv ℝ q (t, s) (1, 0)
  let J : ℝ → E := fun r => fderiv ℝ (fun s => q (r, s)) 0 1
  have hn : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), DifferentiableAt ℝ q p :=
    ((hq.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by decide)).mono
      fun p hp => hp.differentiableAt one_ne_zero
  have hZeq : Z =ᶠ[𝓝 0] (fun s => deriv (fun r => q (r, s)) t) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with s hs
    exact ((hs.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))).deriv).symm
  have hZsmooth : ContDiffAt ℝ ∞ Z 0 :=
    ((hq.fderiv_right (by simp)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  have hZ : HasDerivAt (fun s => deriv (fun r => q (r, s)) t) (deriv Z 0) 0 :=
    (hZsmooth.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq hZeq.symm
  have hparam : HasDerivAt (fun s => q (t, s)) (J t) 0 := by
    simpa only [J, fderiv_eq_smul_deriv, one_smul, Function.comp_def] using
      ((hq.comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
        (by simp)).hasDerivAt
  have htime := ((hq.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ))))
  have hJ : HasDerivAt J (deriv Z 0) t := by
    have hh := Poincare.Analysis.hasDerivAt_fderiv_time_of_eventually hq
      (show ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun r => q (r, s)) (Z s) t from ?_)
      (1 : ℝ)
    · simpa only [J, fderiv_eq_smul_deriv, one_smul] using hh
    · filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with s hs
      exact hs.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))
  have hmetric (u v d : E) :
      fderiv ℝ B (q (t, 0)) d u v =
        B (q (t, 0)) (coordinateChristoffel B (q (t, 0)) d u) v +
          B (q (t, 0)) u (coordinateChristoffel B (q (t, 0)) d v) :=
    fderiv_metric_eq_christoffel hB hinv hsymm u v d
  have hBp : HasDerivAt (fun s => B (q (t, s)))
      (fderiv ℝ B (q (t, 0)) (J t)) 0 := hB.hasFDerivAt.comp_hasDerivAt 0 hparam
  have hE := ((hBp.clm_apply hZ).clm_apply hZ).unique henergy
  simp only [add_apply] at hE
  rw [hmetric, hsymm.self_of_nhds _ (deriv (fun r => q (r, 0)) t),
    hsymm.self_of_nhds (deriv Z 0) _] at hE
  have hsymΓ := christoffelBilinear_symm hB hsymm (J t)
    (deriv (fun r => q (r, 0)) t)
  simp only [christoffelBilinear_apply] at hsymΓ
  rw [hsymΓ] at hE
  have htime' : HasDerivAt (fun r => q (r, 0))
      (deriv (fun r => q (r, 0)) t) t := htime.differentiableAt.hasDerivAt
  have hh := (((hB.hasFDerivAt.comp_hasDerivAt t htime').clm_apply hgeo).clm_apply hJ)
  apply hh.congr_deriv
  simp only [add_apply, map_neg, neg_apply, Function.comp_def]
  rw [hmetric]
  linarith

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem chart_velocity_eq_deriv {q : ℝ → M} {a : M} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) =
        deriv ((extChartAt (𝓡 n) a) ∘ q) t := by
  have hd := mfderiv_comp t
    (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha))
    (hq.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hd1 := (congrArg (fun L => L 1) hd).symm
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) =
    fderiv ℝ ((extChartAt (𝓡 n) a) ∘ q) t 1 at hd1
  simpa only [fderiv_eq_smul_deriv, one_smul] using hd1



theorem hasDerivAt_manifold_variation_pairing
    (g : RiemannianMetric n M) {u : ℝ × ℝ → M} {A : Set (ℝ × ℝ)}
    (hA : IsOpen A) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ u A)
    (hgeo : g.IsGeodesicOn (fun r => u (r, 0)) {r | (r, (0 : ℝ)) ∈ A})
    {t K : ℝ} (ht : (t, (0 : ℝ)) ∈ A)
    (henergy : HasDerivAt
      (fun s => g.inner (u (t, s))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r => u (r, s)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r => u (r, s)) t 1)) (2 * K) 0) :
    HasDerivAt
      (fun r => g.inner (u (r, 0))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => u (z, 0)) r 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (r, s)) 0 1)) K t := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let a := u (t, 0)
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let q := c ∘ u
  have hut := hu.contMDiffAt (hA.mem_nhds ht)
  have hnear : A ∩ u ⁻¹' c.source ∈ 𝓝 (t, (0 : ℝ)) :=
    inter_mem (hA.mem_nhds ht) (hut.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
  obtain ⟨I, S, hI, htI, hS, h0S, hsub⟩ := mem_nhds_prod_iff'.mp hnear
  have hmem {r s : ℝ} (hr : r ∈ I) (hs : s ∈ S) : u (r, s) ∈ c.source :=
    (hsub ⟨hr, hs⟩).2
  have hus {r s : ℝ} (hr : r ∈ I) (hs : s ∈ S) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ u (r, s) :=
    hu.contMDiffAt (hA.mem_nhds (hsub ⟨hr, hs⟩).1)
  have hq : ContDiffAt ℝ ∞ q (t, 0) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (by
      simpa only [c, extChartAt_source] using hmem htI h0S)).comp _ hut
  have htime {r s : ℝ} (hr : r ∈ I) (hs : s ∈ S) :
      mfderiv (𝓡 n) (𝓡 n) c (u (r, s))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => u (z, s)) r 1) =
      deriv (fun z => q (z, s)) r := by
    exact chart_velocity_eq_deriv ((hus hr hs).comp r
      (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.prodMk contDiffAt_const))) (hmem hr hs)
  have hparam {r s : ℝ} (hr : r ∈ I) (hs : s ∈ S) :
      mfderiv (𝓡 n) (𝓡 n) c (u (r, s))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => u (r, z)) s 1) =
      deriv (fun z => q (r, z)) s := by
    exact chart_velocity_eq_deriv ((hus hr hs).comp s
      (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_id))) (hmem hr hs)
  have hpair {r : ℝ} (hr : r ∈ I) :
      g.inner (u (r, 0))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => u (z, 0)) r 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (r, s)) 0 1) =
      B (q (r, 0)) (deriv (fun z => q (z, 0)) r)
        (fderiv ℝ (fun s => q (r, s)) 0 1) := by
    have hh := chartField_inner g
      (q := fun z => u (z, 0))
      (fun z => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => u (z, 0)) z 1)
      (fun z => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (z, s)) 0 1) (hmem hr h0S)
    dsimp only [chartField] at hh
    rw [htime hr h0S, hparam hr h0S] at hh
    simpa only [B, q, c, Function.comp_def, fderiv_eq_smul_deriv, one_smul] using hh.symm
  have hE : HasDerivAt
      (fun s => B (q (t, s)) (deriv (fun r => q (r, s)) t)
        (deriv (fun r => q (r, s)) t)) (2 * K) 0 := by
    apply henergy.congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds h0S] with s hs
    have hh := chartField_inner g (q := fun s => u (t, s))
      (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r => u (r, s)) t 1)
      (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r => u (r, s)) t 1) (hmem htI hs)
    dsimp only [chartField] at hh
    rw [htime htI hs] at hh
    exact hh
  have hgeolocal : g.IsGeodesicOn (fun r => u (r, 0)) I :=
    fun r hr => hgeo r (hsub ⟨hr, h0S⟩).1
  have hgeocoord := (hgeolocal.hasDerivAt_in_chart hI a
    (fun r hr => hmem hr h0S) t htI).2
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds (c.map_source (hmem htI h0S)))
  have hh := hasDerivAt_coordinate_variation_pairing (B := B) (q := q) hq (hB.differentiableAt (by simp))
    (g.isInvertible_chartCoefficients a (c.map_source (hmem htI h0S)))
    (Eventually.of_forall (fun _ v w => g.symm _ _ _)) hgeocoord hE
  apply hh.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds htI] with r hr
  exact hpair hr



theorem gauss_identity_of_radial_family
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) t 1) = ‖v‖)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.ball 0 R)
    (w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients e v v w = inner ℝ v w := by
  let u : ℝ × ℝ → M := fun z => e (z.1 • (v + z.2 • w))
  let A : Set (ℝ × ℝ) := {z | z.1 • (v + z.2 • w) ∈ Metric.ball 0 R}
  let F : ℝ → ℝ := fun t => g.inner (u (t, 0))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r => u (r, 0)) t 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (t, s)) 0 1)
  have hA : IsOpen A := Metric.isOpen_ball.preimage (by fun_prop)
  have hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ u A := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun _ hz => hz
  have hgeo' : g.IsGeodesicOn (fun r => u (r, 0)) {r | (r, (0 : ℝ)) ∈ A} := by
    simpa only [u, A, mem_ofPred_eq, zero_smul, add_zero] using hgeo v hv
  have htime {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (t, (0 : ℝ)) ∈ A := by
    simp only [A, zero_smul, add_zero, mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (inner ℝ v w) t := by
    intro t ht
    apply hasDerivAt_manifold_variation_pairing g hA hu hgeo' (htime ht)
    have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
    have hnorm : HasDerivAt (fun s : ℝ => inner ℝ (v + s • w) (v + s • w))
        (2 * inner ℝ v w) 0 := by
      convert! hline.inner ℝ hline using 1
      simp only [zero_smul, add_zero, real_inner_comm w v]
      ring
    apply hnorm.congr_of_eventuallyEq
    have hnear : ∀ᶠ s : ℝ in 𝓝 0, v + s • w ∈ Metric.ball 0 R :=
      hline.continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (by simpa using hv))
    filter_upwards [hnear] with s hs
    have hsq := congrArg (fun z : ℝ => z ^ 2) (hspeed _ hs t ht)
    rw [RiemannianMetric.tangentNorm, Real.sq_sqrt] at hsq
    · simpa only [u, real_inner_self_eq_norm_sq] using hsq
    · by_cases hz : mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (fun r : ℝ => e (r • (v + s • w))) t 1 = 0
      · simp only [hz, map_zero, le_refl]
      · exact (g.pos _ _ hz).le
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r => F r - r * inner ℝ v w) 0 t := by
    intro t ht
    convert! (hF t ht).sub ((hasDerivAt_id t).mul_const (inner ℝ v w)) using 1
    simp
  have hconst := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ : ℝ => (0 : ℝ))
    (fun t ht => (hdiff t ht).hasDerivWithinAt)
    (fun _ _ => le_refl ‖(0 : ℝ)‖) (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hzero : F 0 = 0 := by
    dsimp only [F, u]
    rw [RiemannianMetric.radialVariation_field_zero]
    exact map_zero _
  have hendpoint : F 1 = inner ℝ v w := by
    simpa only [norm_zero, zero_mul, one_mul, hzero, sub_zero,
      norm_le_zero_iff, sub_eq_zero] using hconst
  have hev := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp)
  have hvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) 1 1 =
      mfderiv (𝓡 n) (𝓡 n) e v v := by
    have hline : HasDerivAt (fun r : ℝ => r • v) v 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
    have hd := mfderiv_comp 1 (by simpa using hev) hline.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun L => L 1) hd
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) 1 1 =
      mfderiv (𝓡 n) (𝓡 n) e ((1 : ℝ) • v)
        (fderiv ℝ (fun r : ℝ => r • v) 1 1) at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hline.deriv] at hd1
    erw [one_smul] at hd1
    exact hd1
  change g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
    (mfderiv (𝓡 n) (𝓡 n) e v w) = _
  change g.inner (e ((1 : ℝ) • (v + (0 : ℝ) • w)))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • (v + (0 : ℝ) • w))) 1 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e ((1 : ℝ) • (v + s • w))) 0 1) = _ at hendpoint
  erw [zero_smul, add_zero] at hendpoint
  erw [hvel, RiemannianMetric.radialVariation_field_one v w hev] at hendpoint
  erw [one_smul] at hendpoint
  exact hendpoint

end PoincareConjecture.CoordinateExponential
