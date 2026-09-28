import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineInjectivity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]


theorem contMDiff_symm_of_line_coordinate (e : ℝ ≃ M)
    (he : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e)
    (hne : ∀ t, deriv (fun u => extChartAt (𝓡 1) (e t) (e u)) t ≠ 0) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e.symm := by
  intro p
  let t := e.symm p
  have hpt : e t = p := e.apply_symm_apply p
  let c := extChartAt (𝓡 1) p
  let F : ℝ → EuclideanSpace ℝ (Fin 1) := fun u => c (e u)
  have hp : e t ∈ c.source := by rw [hpt]; exact mem_extChartAt_source p
  have hF : ContDiffAt ℝ ∞ F t := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (I := 𝓡 1) (n := ∞)
      (by simpa only [c, extChartAt_source] using hp)).comp t (he t))
  have hd := (hF.differentiableAt (by simp)).hasDerivAt
  have hw : deriv F t ≠ 0 := by simpa only [F, c, hpt] using hne t
  let L := ContinuousLinearMap.toSpanSingleton ℝ (deriv F t)
  have hL : Function.Bijective L := ⟨smul_left_injective ℝ hw, fun w =>
    exists_smul_eq_of_finrank_eq_one
      (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)
      hw w⟩
  let A : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv
  have hdA : HasFDerivAt F (A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) t := hd.hasFDerivAt
  let f := hF.toOpenPartialHomeomorph F hdA (by simp)
  have hft : t ∈ f.source := hF.mem_toOpenPartialHomeomorph_source hdA (by simp)
  have hcp : c p = F t := by dsimp only [F]; rw [hpt]
  have htarget : F t ∈ f.target := f.map_source hft
  have hinv : ContDiffAt ℝ ∞ f.symm (F t) := hF.to_localInverse hdA (by simp)
  have hcomp : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun q => f.symm (c q)) p := by
    have hinv' : ContDiffAt ℝ ∞ f.symm (c p) := hcp ▸ hinv
    exact hinv'.contMDiffAt.comp p (contMDiffAt_extChartAt' (mem_chart_source _ p))
  have hγsrc : ∀ᶠ r in 𝓝 t, e r ∈ c.source :=
    (he t).continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hp)
  have hsrc : ∀ᶠ y in 𝓝 (F t), e (f.symm y) ∈ c.source := by
    have htinv : f.symm (F t) = t := f.left_inv hft
    apply (hinv.continuousAt.tendsto.mono_right ?_).eventually hγsrc
    rw [htinv]
  have hccont : ContinuousAt c p := (contMDiffAt_extChartAt' (I := 𝓡 1)
    (n := ∞) (mem_chart_source _ p)).continuousAt
  have hnear : e.symm =ᶠ[𝓝 p] fun q => f.symm (c q) := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓡 1) p).mem_nhds
      (mem_extChartAt_source (I := 𝓡 1) p),
      hccont.preimage_mem_nhds (by rw [hcp]; exact f.open_target.mem_nhds htarget),
      (show Tendsto c (𝓝 p) (𝓝 (F t)) by rw [← hcp]; exact hccont).eventually hsrc]
      with q hq hqtar hqsrc
    apply e.injective
    rw [e.apply_symm_apply]
    apply c.injOn hq hqsrc
    exact (f.right_inv hqtar).symm
  exact hcomp.congr_of_eventuallyEq hnear


theorem metric_eq_of_unit_speed_line_coordinate (g : RiemannianMetric 1 M)
    (e : ℝ ≃ M) (he : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e)
    (hi : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e.symm)
    (hunit : ∀ t, g.tangentNorm (e t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) e t 1) = 1)
    (x : M) (v w : TangentSpace (𝓡 1) x) :
    g.inner x v w = mvfderiv (𝓡 1) e.symm x v * mvfderiv (𝓡 1) e.symm x w := by
  obtain ⟨t, rfl⟩ := e.surjective x
  let V := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) e t 1
  have hVunit : g.inner (e t) V V = 1 := by
    have hh := congrArg (fun r : ℝ => r ^ 2) (hunit t)
    have hpos : 0 ≤ g.inner (e t) V V := by
      by_cases hz : V = 0
      · simp [hz]
      · exact (g.pos _ _ hz).le
    rw [tangentNorm, Real.sq_sqrt hpos] at hh
    simpa only [one_pow] using hh
  have hVne : V ≠ 0 := by
    intro hz
    simp only [hz, map_zero] at hVunit
    exact zero_ne_one hVunit
  have heq : e.symm ∘ e = id := funext e.symm_apply_apply
  have hd := congrArg (fun L => L 1) (mvfderiv_comp t
    (hi.mdifferentiable (by simp) (e t)) (he.mdifferentiable (by simp) t))
  rw [heq, mvfderiv, mfderiv_id] at hd
  have hVcoord : mvfderiv (𝓡 1) e.symm (e t) V = 1 := hd.symm
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := finrank_euclideanSpace_fin
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hVne v
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one hdim hVne w
  rw [← ha, ← hb]
  simp only [map_smul, smul_apply, smul_eq_mul, hVunit, hVcoord, mul_one]
  exact mul_comm b a

variable [T3Space M] [PreconnectedSpace M] [NoncompactSpace M]



theorem exists_metric_line_coordinate (g : RiemannianMetric 1 M) (hc : MetricComplete g) :
    ∃ e : M ≃ ℝ, ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e.symm ∧
      ∀ x (v w : TangentSpace (𝓡 1) x),
        g.inner x v w = mvfderiv (𝓡 1) e x v * mvfderiv (𝓡 1) e x w := by
  classical
  have : Nonempty M := by
    by_contra hn
    have : IsEmpty M := not_nonempty_iff.mp hn
    exact noncompact_univ M isCompact_univ
  let p : M := Classical.arbitrary M
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 1))
  let s := g.tangentNorm p v
  have hs : 0 < s := Real.sqrt_pos.mpr (g.pos p v hv)
  let w := s⁻¹ • v
  have hw : w ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hv
  have hnorm : g.tangentNorm p w = 1 := by
    simp only [w, tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos (inv_pos.mpr hs)]
    exact inv_mul_cancel₀ hs.ne'
  obtain ⟨γ, hγsmooth, hγbij, hγ, hγ0, hγd⟩ :=
    g.exists_smooth_bijective_line_geodesic hc p w hw
  let e := Equiv.ofBijective γ hγbij
  have he : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e := hγsmooth
  have hunit : ∀ t, g.tangentNorm (e t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) e t 1) = 1 := by
    intro t
    exact (line_geodesic_speed g hγ hγ0 hγd t).trans hnorm
  have hne : ∀ t, deriv (fun u => extChartAt (𝓡 1) (e t) (e u)) t ≠ 0 := by
    intro t hz
    have hnormt := (line_geodesic_chart_speed g hγ
      (hγ.hasDerivAt_chart_at (mem_univ t) (γ t) (mem_extChartAt_source _)).1).trans
        (hunit t)
    change deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t = 0 at hz
    simp only [hz, tangentNorm, map_zero, Real.sqrt_zero] at hnormt
    exact zero_ne_one hnormt
  have hi := contMDiff_symm_of_line_coordinate e he hne
  exact ⟨e.symm, hi, he, metric_eq_of_unit_speed_line_coordinate g e he hi hunit⟩

end PoincareConjecture.RiemannianMetric
