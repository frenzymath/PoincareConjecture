import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarSupportedAreaApproximation
import PoincareConjecture.Proofs.M40.Mathlib.ChartPerturbation
import PoincareConjecture.Proofs.M60.Mathlib.ChartApproximation
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PiecewiseArea














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem scalar_exists_chart_area_replacements
    (g : RiemannianMetric n M) (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (f : Plane → M) {O V : Set Plane} (hO : IsOpen O) (hV : IsOpen V)
    (hf : ContinuousOn f O) (hfV : MapsTo f V e.source)
    {L : ℝ≥0} (hcoord : LipschitzOnWith L (e ∘ f) V)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hcompact : HasCompactSupport rho) (hrange : ∀ x, rho x ∈ Icc 0 1)
    (hsupp : tsupport rho ⊆ V) :
    ∃ G : ℕ → Plane → M, ∃ B : ℝ≥0,
      (∀ j, ContinuousOn (G j) O) ∧
      (∀ j, LipschitzOnWith B (e ∘ G j) V) ∧
      (∀ j, MapsTo (G j) V e.source) ∧
      (∀ j x, x ∉ tsupport rho → G j =ᶠ[𝓝 x] f) ∧
      (∀ j x, ContMDiffAt (𝓡 2) (𝓡 n) 1 f x → ContMDiffAt (𝓡 2) (𝓡 n) 1 (G j) x) ∧
      (∀ j x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt (𝓡 2) (𝓡 n) 1 (G j) x) ∧
      TendstoUniformly G f atTop ∧
      (∀ j, IntegrableOn (m60AreaDensity g (G j)) (tsupport rho)) ∧
      Tendsto (fun j => ∫ x in tsupport rho, m60AreaDensity g (G j) x) atTop
        (𝓝 (∫ x in tsupport rho, m60AreaDensity g f x)) := by
  obtain ⟨u, hu, heq⟩ := hcoord.extend_finite_dimension
  have huV : MapsTo u V e.target := by
    intro x hx
    rw [← heq hx]
    exact e.map_source (hfV hx)
  have huK : MapsTo u (tsupport rho) e.target := fun _ hx => huV (hsupp hx)
  obtain ⟨v, B, hv, hvK, haway, hpreserve, hsmooth, hval, -, harea⟩ :=
    scalar_exists_supported_area_approximation g e.open_target hei hu hcompact huK
      hrho hcompact hrange
  let G := fun j => M40.chartPerturb e V f (v j - u)
  have hvV (j : ℕ) : MapsTo (v j) V e.target := by
    intro x hx
    by_cases hxs : x ∈ tsupport rho
    · exact hvK j hxs
    · rw [(haway j x hxs).self_of_nhds]
      exact huV hx
  have hGnear (j : ℕ) {x : Plane} (hx : x ∈ V) :
      G j =ᶠ[𝓝 x] e.symm ∘ v j := by
    filter_upwards [hV.mem_nhds hx] with y hy
    change M40.chartPerturb e V f (v j - u) y = e.symm (v j y)
    rw [M40.chartPerturb_of_mem e V f (v j - u) hy]
    simp only [Pi.sub_apply, ← heq hy, Function.comp_apply]
    congr 1
    abel
  have hGaway (j : ℕ) (x : Plane) (hx : x ∉ tsupport rho) :
      G j =ᶠ[𝓝 x] f := by
    filter_upwards [haway j x hx] with y hy
    exact M40.chartPerturb_eq_of_zero e V f (v j - u) hfV
      (by simp only [Pi.sub_apply, hy, sub_self])
  have hfnear {x : Plane} (hx : x ∈ V) : f =ᶠ[𝓝 x] e.symm ∘ u := by
    filter_upwards [hV.mem_nhds hx] with y hy
    change f y = e.symm (u y)
    rw [← heq hy]
    exact (e.left_inv (hfV hy)).symm
  have hGcoord (j : ℕ) {x : Plane} (hx : x ∈ V) : e (G j x) = v j x := by
    rw [(hGnear j hx).self_of_nhds]
    exact e.right_inv (hvV j hx)
  have hGa (j : ℕ) : EqOn (m60AreaDensity g (G j))
      (m60AreaDensity g (e.symm ∘ v j)) (tsupport rho) :=
    fun _ hx => m60AreaDensity_congr_of_eventuallyEq g (hGnear j (hsupp hx))
  have hfa : EqOn (m60AreaDensity g f) (m60AreaDensity g (e.symm ∘ u)) (tsupport rho) :=
    fun _ hx => m60AreaDensity_congr_of_eventuallyEq g (hfnear (hsupp hx))
  refine ⟨G, B, ?_, ?_, ?_, hGaway, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases hxs : x ∈ tsupport rho
    · have hc := ((e.continuousAt_symm (hvV j (hsupp hxs))).comp
        (hv j).continuous.continuousAt).congr_of_eventuallyEq (hGnear j (hsupp hxs))
      exact hc.continuousWithinAt
    · have hc := (hf.continuousAt (hO.mem_nhds hx)).congr_of_eventuallyEq (hGaway j x hxs)
      exact hc.continuousWithinAt
  · intro j x hx y hy
    change edist (e (G j x)) (e (G j y)) ≤ _
    rw [hGcoord j hx, hGcoord j hy]
    exact hv j x y
  · intro j x hx
    rw [(hGnear j hx).self_of_nhds]
    exact e.map_target (hvV j hx)
  · intro j x hfx
    by_cases hxs : x ∈ tsupport rho
    · have hx := hsupp hxs
      have huc : ContMDiffAt (𝓡 2) (𝓡 n) 1 u x := by
        apply ((he.contMDiffAt (e.open_source.mem_nhds (hfV hx))).comp x hfx).congr_of_eventuallyEq
        filter_upwards [hV.mem_nhds hx] with y hy
        exact (heq hy).symm
      have hvc := contMDiffAt_iff_contDiffAt.mpr (hpreserve j x (contMDiffAt_iff_contDiffAt.mp huc))
      exact ((hei.contMDiffAt (e.open_target.mem_nhds (hvV j hx))).comp x hvc).congr_of_eventuallyEq
        (hGnear j hx)
    · exact hfx.congr_of_eventuallyEq (hGaway j x hxs)
  · intro j x hx
    have hxs : x ∈ tsupport rho := subset_tsupport rho
      (Function.mem_support.mpr (by rw [hx.self_of_nhds]; exact one_ne_zero))
    have hvc : ContMDiffAt (𝓡 2) (𝓡 n) 1 (v j) x :=
      contMDiffAt_iff_contDiffAt.mpr ((hsmooth j x hx).of_le (by simp))
    have hc := (hei.contMDiffAt (e.open_target.mem_nhds (hvV j (hsupp hxs)))).comp x hvc
    exact hc.congr_of_eventuallyEq (hGnear j (hsupp hxs))
  · apply Metric.tendstoUniformly_iff.mpr
    intro eps heps
    obtain ⟨delta, hdelta, hcontrol⟩ := M60.exists_pos_inverse_chart_control e
      (hcompact.image hu.continuous) (by rintro _ ⟨x, hx, rfl⟩; exact huK hx) heps
    filter_upwards [(Metric.tendstoUniformly_iff.mp hval) delta hdelta] with j hj x
    by_cases hx : x ∈ tsupport rho
    · rw [(hGnear j (hsupp hx)).self_of_nhds, (hfnear (hsupp hx)).self_of_nhds]
      exact (dist_comm _ _).trans_lt (hcontrol (u x) (mem_image_of_mem u hx) (v j x)
        ((dist_comm _ _).trans_lt (hj x))).2
    · rw [(hGaway j x hx).self_of_nhds, dist_self]
      exact heps
  · intro j
    apply (scalarC1_composed_area_integrable g e.open_target hei (hv j) hcompact (hvK j)).congr
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with x hx
    exact (hGa j hx).symm
  · have hGi (j : ℕ) := setIntegral_congr_fun (μ := volume) hcompact.measurableSet (hGa j)
    have hfi := setIntegral_congr_fun (μ := volume) hcompact.measurableSet hfa
    simpa only [hGi, hfi] using harea

end PoincareConjecture.M64Uniformization
