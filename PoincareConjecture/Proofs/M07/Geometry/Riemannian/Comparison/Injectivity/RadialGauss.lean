import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Nonconjugacy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CovariantPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionVariation ConnectionAlongCurve CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem chartField_velocity_eq_deriv {q : ℝ → M} {a : M} {t : ℝ}
    (hq : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) t =
      deriv ((extChartAt (𝓡 n) a) ∘ q) t := by
  have hd := mfderiv_comp t
    (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha)) hq
  rw [mfderiv_eq_fderiv] at hd
  have hd1 := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => A 1) hd
  change fderiv ℝ ((extChartAt (𝓡 n) a) ∘ q) t 1 = _ at hd1
  rw [fderiv_eq_smul_deriv, one_smul] at hd1
  exact hd1.symm

theorem contDiffAt_chartField_velocity_at {q : ℝ → M} {a : M} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞
      (chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)) t := by
  have hchart := contDiffAt_chart_curve hq ha
  have hd := ((hchart.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := (1 : ℝ))))
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hq.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  apply hd.congr_of_eventuallyEq
  filter_upwards [hnear, hq.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source a).mem_nhds ha)] with s hs hsa
  rw [chartField_velocity_eq_deriv (hs.mdifferentiableAt (by simp)) hsa,
    fderiv_eq_smul_deriv, one_smul]

theorem IsGeodesicOn.manifoldCovDerivAlong_velocity_eq_zero
    {g : RiemannianMetric n M} {q : ℝ → M} {I : Set ℝ}
    (hgeo : g.IsGeodesicOn q I) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) {t : ℝ} (ht : t ∈ I) :
    manifoldCovDerivAlong g q (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) 1 t = 0 := by
  let a := q t
  let c := extChartAt (𝓡 n) a
  let U := I ∩ q ⁻¹' c.source
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hI (isOpen_extChartAt_source a)
  have htU : t ∈ U := ⟨ht, mem_extChartAt_source _⟩
  have hgU : g.IsGeodesicOn q U := fun s hs => hgeo s hs.1
  have hd := hgU.hasDerivAt_in_chart hU a (fun s hs => hs.2) t htU
  have hqt := hq.contMDiffAt (hI.mem_nhds ht)
  have hfield : chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) =ᶠ[𝓝 t]
      deriv (c ∘ q) := by
    filter_upwards [hU.mem_nhds htU] with s hs
    exact chartField_velocity_eq_deriv
      ((hq.contMDiffAt (hI.mem_nhds hs.1)).mdifferentiableAt (by simp)) hs.2
  apply (isInvertible_mfderiv_extChartAt (I := 𝓡 n) (mem_extChartAt_source (q t))).injective
  rw [map_zero]
  rw [manifoldCovDerivAlong_in_chart g a (mem_extChartAt_source _) hqt.continuousAt
    ((contDiffAt_chart_curve hqt (mem_extChartAt_source _)).differentiableAt (by simp))
    ((contDiffAt_chartField_velocity_at hqt (mem_extChartAt_source _)).differentiableAt (by simp))]
  change covDerivAlong (christoffelBilinear (g.pullbackCoefficients c.symm)) (c ∘ q)
    (chartField q a (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)) 1 t = 0
  rw [covDerivAlong_congr _ _ hfield, covDerivAlong, fderiv_eq_smul_deriv, one_smul]
  change deriv (deriv (c ∘ q)) t +
    coordinateChristoffel (g.pullbackCoefficients c.symm) (c (q t))
      (fderiv ℝ (c ∘ q) t 1) (deriv (c ∘ q) t) = 0
  rw [fderiv_eq_smul_deriv, one_smul]
  exact add_eq_zero_iff_eq_neg.mpr hd.2.deriv

theorem inner_velocity_jacobi_eq_mul_initial
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {q : ℝ → M} {I : Set ℝ} {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    (hI : IsOpen I) (hconn : IsPreconnected I) (h0 : (0 : ℝ) ∈ I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hgeo : g.IsGeodesicOn q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ I, manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
      -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) (hJ0 : J 0 = 0)
    {t : ℝ} (ht : t ∈ I) :
    g.inner (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (J t) =
      t * g.inner (q 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1)
        (manifoldCovDerivAlong g q J 1 0) := by
  let V : (s : ℝ) → TangentSpace (𝓡 n) (q s) :=
    fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1
  let A : ℝ → ℝ := fun s => g.inner (q s) (V s) (manifoldCovDerivAlong g q J 1 s)
  let B : ℝ → ℝ := fun s => g.inner (q s) (V s) (J s)
  have hV s (hs : s ∈ I) : ContDiffAt ℝ ∞ (chartField q (q s) V) s :=
    contDiffAt_chartField_velocity_at (hq.contMDiffAt (hI.mem_nhds hs)) (mem_extChartAt_source _)
  have hDV s (hs : s ∈ I) : manifoldCovDerivAlong g q V 1 s = 0 :=
    hgeo.manifoldCovDerivAlong_velocity_eq_zero hI hq hs
  have hA s (hs : s ∈ I) : HasDerivAt A 0 s := by
    have h := hasDerivAt_metric_inner_along g (hq.contMDiffAt (hI.mem_nhds hs)) (hV s hs)
      (contDiffAt_chartField_covDeriv g hI hq hJ hs (mem_extChartAt_source _))
    change HasDerivAt A
      (g.inner (q s) (manifoldCovDerivAlong g q V 1 s) (manifoldCovDerivAlong g q J 1 s) +
        g.inner (q s) (V s) (manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 s)) s at h
    rw [hDV s hs, hjac s hs, map_zero, zero_apply, zero_add, map_neg] at h
    have hskew := D.curvatureTensor_swap_last (q s) (J s) (V s) (V s) (V s)
    have hz : g.inner (q s) (V s) (D.curvature (q s) (J s) (V s) (V s)) = 0 := by
      rw [g.symm]
      change D.curvatureTensor (q s) (J s) (V s) (V s) (V s) = 0
      linarith
    simpa only [V, hz, neg_zero] using h
  have hAconst s (hs : s ∈ I) : A s = A 0 :=
    hI.is_const_of_deriv_eq_zero hconn
      (fun u hu => (hA u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hA u hu).deriv) hs h0
  have hB s (hs : s ∈ I) : HasDerivAt B (A 0) s := by
    have h := hasDerivAt_metric_inner_along g (hq.contMDiffAt (hI.mem_nhds hs))
      (hV s hs) (hJ s hs)
    change HasDerivAt B (g.inner (q s) (manifoldCovDerivAlong g q V 1 s) (J s) + A s) s at h
    rw [hDV s hs, map_zero, zero_apply, zero_add, hAconst s hs] at h
    exact h
  have hlinear s : HasDerivAt (fun u : ℝ => u * A 0) (A 0) s := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id s).mul_const (A 0)
  have heq := hI.eqOn_of_deriv_eq hconn
    (fun u hu => (hB u hu).differentiableAt.differentiableWithinAt)
    (fun u _ => (hlinear u).differentiableAt.differentiableWithinAt)
    (fun u hu => (hB u hu).deriv.trans (hlinear u).deriv.symm) h0
    (show B 0 = (0 : ℝ) * A 0 by simp [B, hJ0])
  exact heq ht

theorem radial_gauss_identity
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.ball 0 R)
    (w : EuclideanSpace ℝ (Fin n)) :
    g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
      (mfderiv (𝓡 n) (𝓡 n) e v w) = inner ℝ v w := by
  obtain ⟨S, a, hS, h0, ha, hvary, hdom⟩ := exists_radial_variation_rectangle hv w
  let q : ℝ → M := fun t => e (t • v)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (q t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q (Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · intro t ht
      exact (by simpa only [zero_smul, add_zero] using hdom 0 h0 t ht :
        t • v ∈ Metric.ball 0 R)
  have hJ : ∀ t ∈ Ioo (-a : ℝ) a, ContDiffAt ℝ ∞ (chartField q (q t) J) t := by
    intro t ht
    apply contDiffAt_chartField_radialVariation_of_ball he v w
    exact (by simpa only [zero_smul, add_zero] using hdom 0 h0 t ht :
      t • v ∈ Metric.ball 0 R)
  have hgeo' : g.IsGeodesicOn q (Ioo (-a : ℝ) a) := by
    intro t ht
    exact hgeo v hv t (by
      change t • v ∈ Metric.ball 0 R
      simpa only [zero_smul, add_zero] using hdom 0 h0 t ht)
  have hjac : ∀ t ∈ Ioo (-a : ℝ) a,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    intro t ht
    have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
        (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ Ioo (-a) a) := by
      apply he.comp
      · apply contMDiffOn_iff_contDiffOn.mpr; fun_prop
      · exact fun z hz => hdom z.1 hz.1 z.2 hz.2
    have hvar : ∀ s ∈ S, g.IsGeodesicOn
        (fun r : ℝ => e (r • (v + s • w))) (Ioo (-a) a) :=
      fun s hs r hr => hgeo _ (hvary s hs) r (hdom s hs r hr)
    have hj := manifoldVariation_jacobi g D hS isOpen_Ioo h0 hsmooth hvar
      (show t ∈ Ioo (-a) a by exact ht)
    dsimp only at hj
    rw [show v + (0 : ℝ) • w = v by simp] at hj
    exact eq_neg_of_add_eq_zero_left hj
  have hinner := inner_velocity_jacobi_eq_mul_initial g D isOpen_Ioo
    (convex_Ioo (-a) a).isPreconnected (by constructor <;> linarith)
    hq hgeo' hJ hjac (radialVariation_field_zero e v w)
    (show (1 : ℝ) ∈ Ioo (-a) a by exact ⟨by linarith [ha], by linarith [ha]⟩)
  have he0 := he.contMDiffAt (x := 0) (Metric.isOpen_ball.mem_nhds (by
    apply Metric.mem_ball_self
    exact (norm_nonneg v).trans_lt (by simpa using hv)))
  have hzero := radialVariation_initial_covariantDerivative g he0 v w
  have hfield := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hfield
  have hvelocity (t : ℝ) (ht : t • v ∈ Metric.ball 0 R) :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1 = mfderiv (𝓡 n) (𝓡 n) e (t • v) v := by
    have hline : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const v
    have hd := mfderiv_comp t
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds ht)).mdifferentiableAt (by simp))
      hline.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => A 1) hd
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1 =
      mfderiv (𝓡 n) (𝓡 n) e (t • v) (fderiv ℝ (fun s : ℝ => s • v) t 1) at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hline.deriv] at hd1
    exact hd1
  change g.inner (q 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1) (J 1) = _ at hinner
  rw [hfield, hzero, hvelocity 1 (by simpa using hv),
    hvelocity 0 (by simpa using (hdom 0 h0 0 (by constructor <;> linarith)))] at hinner
  have hinit : g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 v)
      (mfderiv (𝓡 n) (𝓡 n) e 0 w) = inner ℝ v w := by
    change g.pullbackCoefficients e 0 v w = inner ℝ v w
    exact hnorm v w
  have hleft := congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner (e z)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e z v)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w)) (one_smul ℝ v)
  have hright := congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner (e z)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e z v)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e 0 w)) (zero_smul ℝ v)
  simp only [one_mul] at hinner
  exact hleft.symm.trans (hinner.trans (hright.trans hinit))

end PoincareConjecture.RiemannianMetric
