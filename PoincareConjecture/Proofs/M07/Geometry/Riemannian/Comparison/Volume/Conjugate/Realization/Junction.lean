import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.SmoothExtension

open Set Filter
open scoped Manifold Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.Conjugate.Realization

open RiemannianMetric ConnectionAlongCurve

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffAt_of_isGeodesicOn [T2Space M]
    {g : RiemannianMetric n M} {γ : ℝ → M} {S : Set ℝ}
    (hγ : g.IsGeodesicOn γ S) {t : ℝ} (ht : t ∈ S) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ t := by
  let p := γ t
  let v := deriv (fun u => extChartAt (𝓡 n) p (γ u)) t
  obtain ⟨V, δ, Φ, hV, hz, _, hδ, hΦ, hinit, hflow⟩ :=
    g.exists_smooth_chart_geodesic_flow p v
  let z := (extChartAt (𝓡 n) p p, v)
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hγ' : g.IsGeodesicOn γ {t} := fun u hu => by
    subst u
    exact hγ t ht
  have heq := hγ'.eq_nhds_chart_flow (convex_singleton t) p hδ
    (fun u hu => ⟨(hflow z hz u hu).1, (hflow z hz u hu).2.1⟩)
    (a := t) (b := t) (mem_singleton t) (mem_singleton t) (mem_extChartAt_source p)
    (hinit z hz) (by simpa only [sub_self] using h0)
  have hread : ContDiffAt ℝ ∞ (fun u : ℝ => Φ (z, u - t)) t := by
    have hΦ0 : ContDiffAt ℝ ∞ Φ (z, t - t) :=
      hΦ.contDiffAt ((hV.prod isOpen_Ioo).mem_nhds (by
        simpa only [sub_self] using
          (show (z, (0 : ℝ)) ∈ V ×ˢ Ioo (-δ) δ from ⟨hz, h0⟩)))
    have htime : ContDiffAt ℝ ∞ (fun u : ℝ => (z, u - t)) t :=
      contDiffAt_const.prodMk (contDiffAt_id.sub contDiffAt_const)
    simpa only [Function.comp_def] using hΦ0.comp t htime
  have htarget : (Φ (z, t - t)).1 ∈ (extChartAt (𝓡 n) p).target := by
    simpa only [sub_self] using (hflow z hz 0 h0).1
  have hsmooth := ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htarget)).comp t
      (contMDiffAt_iff_contDiffAt.mpr hread.fst)
  exact hsmooth.congr_of_eventuallyEq heq

theorem isGeodesicOn_const (g : RiemannianMetric n M) (p : M) (S : Set ℝ) :
    g.IsGeodesicOn (fun _ : ℝ => p) S := by
  intro t ht
  refine ⟨p, fun _ => extChartAt (𝓡 n) p p, fun _ => 0, ?_⟩
  apply Filter.Eventually.of_forall
  intro u
  refine ⟨((extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)).symm,
    mem_extChartAt_target p, hasDerivAt_const u _, ?_⟩
  simpa [coordinateChristoffel, metricKoszulCovector] using
    (hasDerivAt_const u (0 : EuclideanSpace ℝ (Fin n)))

theorem exists_local_junction (g : RiemannianMetric n M) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ (δ : ℝ) (η : ℝ → M), 0 < δ ∧ g.IsGeodesicOn η (Ioo (-δ) δ) ∧
      η 0 = p ∧ HasDerivAt (fun s => extChartAt (𝓡 n) p (η s)) v 0 ∧
      (v = 0 → ∀ s, η s = p) := by
  by_cases hv : v = 0
  · refine ⟨1, fun _ => p, by norm_num, isGeodesicOn_const g p _, rfl, ?_,
      fun _ _ => rfl⟩
    simpa only [hv] using hasDerivAt_const (0 : ℝ) (extChartAt (𝓡 n) p p)
  · obtain ⟨δ, hδ, _, η, hη, hη0, hηv⟩ := g.exists_geodesic_initial_data p v
    exact ⟨δ, η, hδ, hη, hη0, hηv, fun h => (hv h).elim⟩

theorem hasDerivAt_junction_chart
    {g : RiemannianMetric n M} {η : ℝ → M} {S : Set ℝ}
    (hη : g.IsGeodesicOn η S) (h0 : (0 : ℝ) ∈ S) {p β : M}
    (hp : η 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun s => extChartAt (𝓡 n) p (η s)) v 0)
    (hβ : p ∈ (extChartAt (𝓡 n) β).source) :
    HasDerivAt (fun s => extChartAt (𝓡 n) β (η s))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) β) p v) 0 := by
  subst p
  have hd := (hη.contMDiffAt h0).mdifferentiableAt one_ne_zero
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
    (mem_chart_source _ (η 0))).mdifferentiableAt (by simp)
  have heq := congrArg (fun L => L 1) (mfderiv_comp 0 hc hd)
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun u => extChartAt (𝓡 n) (η 0) (η u)) 0 = _ at heq
  rw [hv.deriv] at heq
  change v = (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (η 0)) (η 0))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 0 1) at heq
  have hv' : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 0 1 = v := by
    rw [mfderiv_extChartAt_self] at heq
    exact heq.symm
  have hcβ := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
    (show η 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) β).source by
      simpa only [extChartAt_source] using hβ)).mdifferentiableAt (by simp)
  have hdβ := congrArg (fun L => L 1) (mfderiv_comp 0 hcβ hd)
  rw [mfderiv_eq_fderiv] at hdβ
  change deriv (fun u => extChartAt (𝓡 n) β (η u)) 0 = _ at hdβ
  change deriv (fun u => extChartAt (𝓡 n) β (η u)) 0 =
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) β) (η 0))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 0 1) at hdβ
  rw [hv'] at hdβ
  rw [← hdβ]
  exact (hη.hasDerivAt_chart_at h0 β hβ).1

theorem exists_smooth_junction_reading [T2Space M]
    {g : RiemannianMetric n M} {η : ℝ → M} {δ : ℝ}
    (hδ : 0 < δ) (hη : g.IsGeodesicOn η (Ioo (-δ) δ)) {β : M}
    (hβ : η 0 ∈ (extChartAt (𝓡 n) β).source) :
    ∃ ĉ : ℝ → EuclideanSpace ℝ (Fin n), ContDiff ℝ 3 ĉ ∧
      ĉ =ᶠ[𝓝 (0 : ℝ)] ((extChartAt (𝓡 n) β) ∘ η) ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), η s ∈ (extChartAt (𝓡 n) β).source := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_iff_pos.mpr hδ, hδ⟩
  have hs := (hη.contMDiffAt h0).continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source β).mem_nhds hβ)
  obtain ⟨l, r, h0lr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem (isOpen_Ioo.mem_nhds h0) hs)
  have hsm : ContDiffOn ℝ 3 ((extChartAt (𝓡 n) β) ∘ η) (Ioo l r) := by
    intro t ht
    exact ((contDiffAt_chart_curve (contMDiffAt_of_isGeodesicOn hη (hsub ht).1)
      (hsub ht).2).of_le (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  obtain ⟨ĉ, V, hĉ, hV, h0V, _, heq⟩ :=
    exists_contDiff_eqOn_of_contDiffOn_Ioo hsm h0lr.1 le_rfl h0lr.2
  refine ⟨ĉ, hĉ, ?_, hs⟩
  filter_upwards [hV.mem_nhds (h0V ⟨le_rfl, le_rfl⟩)] with s hs using heq hs

end PoincareConjecture.Conjugate.Realization

end
