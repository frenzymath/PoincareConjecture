import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.LocalInverse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Length










set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric



theorem exists_exponential_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ e : OpenPartialHomeomorph E M,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => c (e v)) (ContinuousLinearMap.id ℝ E) 0 ∧
      ∃ Γ : E × ℝ → E × E,
        ContDiffOn ℝ ∞ Γ (e.source ×ˢ Ioo (-2 : ℝ) 2) ∧
        ∀ v ∈ e.source,
          Γ (v, 0) = (c p, v) ∧ c.symm (Γ (v, 1)).1 = e v ∧
          g.edist p (e v) ≤ ENNReal.ofReal (Real.sqrt (B (c p) v v)) ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Γ (v, t)).1 ∈ c.target ∧
            HasDerivAt (fun s => Γ (v, s)) (coordinateGeodesicField B (Γ (v, t))) t ∧
            B (Γ (v, t)).1 (Γ (v, t)).2 (Γ (v, t)).2 = B (c p) v v := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  have hU : IsOpen c.target := isOpen_extChartAt_target (I := 𝓡 n) p
  have hB : ContDiffOn ℝ ∞ B c.target := g.contDiffOn_chartCoefficients p
  obtain ⟨f, hzero, hfzero, htarget, hf, hfinv, hfd, Γ, hΓ, hcurve⟩ :=
    CoordinateExponential.exists_local_exponential hU hB
      (fun y hy => g.isInvertible_chartCoefficients p hy)
      (fun y _ u v => g.symm _ _ _) (mem_extChartAt_target p)
  let e : OpenPartialHomeomorph E M := f.trans (chartAt E p).symm
  have hsource : e.source = f.source := by
    ext v
    constructor
    · exact fun hv => hv.1
    · intro hv
      refine ⟨hv, ?_⟩
      simpa [c, extChartAt_target] using htarget (f.map_source hv)
  have heapply : ∀ v, e v = c.symm (f v) := fun _ => rfl
  have hezero : e 0 = p := by
    rw [heapply, hfzero]
    exact c.left_inv (mem_extChartAt_source p)
  have hesmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (c.symm ∘ f) e.source
    rw [hsource]
    exact (contMDiffOn_extChartAt_symm p).comp
      (contMDiffOn_iff_contDiffOn.mpr hf) (fun v hv => htarget (f.map_source hv))
  have heinverse : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f.symm ∘ c) e.target
    apply (contMDiffOn_iff_contDiffOn.mpr hfinv).comp
      ((contMDiffOn_extChartAt (I := 𝓡 n) (x := p)).mono (fun y hy => hy.1))
    exact fun y hy => hy.2
  have hcoord : (fun v => c (e v)) =ᶠ[𝓝 0] f := by
    filter_upwards [f.open_source.mem_nhds hzero] with v hv
    exact c.right_inv (htarget (f.map_source hv))
  refine ⟨e, hsource.symm ▸ hzero, hezero, hesmooth, heinverse,
    hfd.congr_of_eventuallyEq hcoord, Γ, hsource.symm ▸ hΓ, ?_⟩
  intro v hv
  have hvf : v ∈ f.source := hsource ▸ hv
  have hcv := hcurve v hvf
  have henergy : ∀ t ∈ Ioo (-2 : ℝ) 2,
      B (Γ (v, t)).1 (Γ (v, t)).2 (Γ (v, t)).2 = B (c p) v v := by
    have hd : ∀ s ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun r => B (Γ (v, r)).1 (Γ (v, r)).2 (Γ (v, r)).2) 0 s := by
      intro s hs
      have hsU := (hcv.2.2 s hs).1
      exact hasDerivAt_coordinate_geodesic_energy
        ((hB _ hsU).contDiffAt (hU.mem_nhds hsU) |>.differentiableAt (by simp))
        (g.isInvertible_chartCoefficients p hsU) (fun u w => g.symm _ _ _)
        (hcv.2.2 s hs).2.fst (hcv.2.2 s hs).2.snd
    intro t ht
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo (-2 : ℝ) 2).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    simpa only [hcv.1] using hconst
  refine ⟨hcv.1, by rw [hcv.2.1, heapply], ?_,
    fun t ht => ⟨(hcv.2.2 t ht).1, (hcv.2.2 t ht).2, henergy t ht⟩⟩
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hq : ContDiffOn ℝ 1 (fun t => (Γ (v, t)).1) (Icc (0 : ℝ) 1) :=
    (hΓ.fst.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun t ht => ⟨hvf, hI ht⟩)).of_le (by simp)
  have hdist := g.edist_chart_curve_le_of_energy p (a := 0) (b := 1) (by norm_num)
    (fun t ht => (hcv.2.2 t (hI ht)).1) hq
    (fun t ht => (hcv.2.2 t (hI ht)).2.fst) (fun t ht => henergy t (hI ht))
  have hcp : (extChartAt (𝓡 n) p).symm ((extChartAt (𝓡 n) p) p) = p :=
    (extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)
  simpa only [hcv.1, hcv.2.1, heapply, hcp,
    sub_zero, ENNReal.ofReal_one, mul_one] using hdist

end PoincareConjecture.RiemannianMetric
