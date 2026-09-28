import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.NormalChart

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M]

theorem endpoint_agreement_of_comparison
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source) (_hep : e 0 = p)
    (_hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0)
    (Γ : EuclideanSpace ℝ (Fin n) → ℝ → M)
    (hcmp : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ η : ℝ → M,
      g.IsGeodesicOn η (Icc (0 : ℝ) 1) ∧ η 0 = p ∧ η 1 = e v ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0)
    (hgeo : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1))
    (hinit : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), Γ v 0 = p)
    (hvel : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      HasDerivAt (fun t => extChartAt (𝓡 n) p (Γ v t)) v 0) :
    (fun v => Γ v 1) =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin n))] e := by
  filter_upwards [hcmp, hgeo, hinit, hvel, e.open_source.mem_nhds he0]
    with v ⟨η, hη, hη0, hη1, hηv⟩ hΓ hΓ0 hΓv hv
  have hsource : Γ v 0 ∈ (extChartAt (𝓡 n) p).source := by
    rw [hΓ0]
    exact mem_extChartAt_source p
  have hlocal : Γ v =ᶠ[𝓝 (0 : ℝ)] η :=
    IsGeodesicOn.eq_nhds_of_initial_data (g := g) (γ := Γ v) (η := η)
      (s := Icc (0 : ℝ) 1) hΓ hη (t₀ := 0) (by norm_num) p
      hsource (hΓ0.trans hη0.symm) (hΓv.deriv.trans hηv.deriv.symm)
  have hend : Γ v 1 = η 1 := by
    exact hΓ.eqOn_of_eq_nhds hη
      (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 0) (by norm_num) hlocal
      ⟨by norm_num, by norm_num⟩
  exact hend.trans hη1

theorem hasFDerivAt_endpoint_of_comparison
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source) (hep : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0)
    (Γ : EuclideanSpace ℝ (Fin n) → ℝ → M)
    (hcmp : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ η : ℝ → M,
      g.IsGeodesicOn η (Icc (0 : ℝ) 1) ∧ η 0 = p ∧ η 1 = e v ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0)
    (hgeo : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1))
    (hinit : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), Γ v 0 = p)
    (hvel : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      HasDerivAt (fun t => extChartAt (𝓡 n) p (Γ v t)) v 0) :
    HasFDerivAt (fun v => extChartAt (𝓡 n) p (Γ v 1))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 := by
  have heq := endpoint_agreement_of_comparison g p e he0 hep hed Γ hcmp hgeo hinit hvel
  exact hed.congr_of_eventuallyEq (heq.fun_comp (extChartAt (𝓡 n) p))



theorem exists_exponential_chart_eq_endpoint_nhds
    (g : RiemannianMetric n M) (p : M)
    (Γ : EuclideanSpace ℝ (Fin n) → ℝ → M)
    (hgeo : ∀ᶠ v in 𝓝 0, g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1))
    (hinit : ∀ᶠ v in 𝓝 0, Γ v 0 = p)
    (hvel : ∀ᶠ v in 𝓝 0,
      HasDerivAt (fun t => extChartAt (𝓡 n) p (Γ v t)) v 0) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      (fun v => Γ v 1) =ᶠ[𝓝 0] e := by
  let c := extChartAt (𝓡 n) p
  obtain ⟨e, he0, hep, hesmooth, heinverse, hederiv, Φ, hΦ, hcurve⟩ :=
    g.exists_exponential_chart p
  refine ⟨e, he0, hep, hesmooth, heinverse, hederiv, ?_⟩
  apply endpoint_agreement_of_comparison g p e he0 hep hederiv Γ ?_ hgeo hinit hvel
  filter_upwards [e.open_source.mem_nhds he0] with v hv
  let η : ℝ → M := fun t => c.symm (Φ (v, t)).1
  have hc := hcurve v hv
  have hηgeo : g.IsGeodesicOn η (Ioo (-2 : ℝ) 2) := by
    exact g.isGeodesicOn_chart_curve p isOpen_Ioo
      (q := fun t => (Φ (v, t)).1) (w := fun t => (Φ (v, t)).2)
      (fun t ht => ⟨(hc.2.2.2 t ht).1, (hc.2.2.2 t ht).2.1.fst,
        (hc.2.2.2 t ht).2.1.snd⟩)
  have hη0 : η 0 = p := by
    dsimp [η]
    rw [hc.1]
    exact c.left_inv (mem_extChartAt_source p)
  have hηv : HasDerivAt (fun t => c (η t)) v 0 := by
    have hq : (fun t => c (η t)) =ᶠ[𝓝 (0 : ℝ)] fun t => (Φ (v, t)).1 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 2)] with t ht
      exact c.right_inv (hc.2.2.2 t ht).1
    have hd : HasDerivAt (fun t => (Φ (v, t)).1) (Φ (v, 0)).2 0 :=
      (hc.2.2.2 0 (by norm_num)).2.1.fst
    have hd' : HasDerivAt (fun t => (Φ (v, t)).1) v 0 := by
      simpa only [hc.1] using hd
    exact hd'.congr_of_eventuallyEq hq
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  exact ⟨η, fun t ht => hηgeo t (hI ht), hη0, hc.2.1, hηv⟩



theorem geodesic_endpoint_zero_and_hasFDerivAt
    (g : RiemannianMetric n M) (p : M)
    (Γ : EuclideanSpace ℝ (Fin n) → ℝ → M)
    (hgeo : ∀ᶠ v in 𝓝 0, g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1))
    (hinit : ∀ᶠ v in 𝓝 0, Γ v 0 = p)
    (hvel : ∀ᶠ v in 𝓝 0,
      HasDerivAt (fun t => extChartAt (𝓡 n) p (Γ v t)) v 0) :
    Γ 0 1 = p ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) p (Γ v 1))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 := by
  obtain ⟨e, _, hep, _, _, hederiv, heq⟩ :=
    g.exists_exponential_chart_eq_endpoint_nhds p Γ hgeo hinit hvel
  exact ⟨heq.self_of_nhds.trans hep,
    hederiv.congr_of_eventuallyEq (heq.fun_comp (extChartAt (𝓡 n) p))⟩

end PoincareConjecture.RiemannianMetric
