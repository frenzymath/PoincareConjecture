import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothingDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suC1_supportedChartSmoothing
    (p : UnitTwoSphere) (b : M) {U : Set UnitTwoSphere} (hU : IsOpen U)
    (hUe : U ⊆ (chartAt LoopPlane p).source)
    {rho : UnitTwoSphere → ℝ} {f : UnitTwoSphere → M}
    {G : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hG : ContDiff ℝ ∞ G) (hsupp : tsupport rho ⊆ U)
    (hfU : MapsTo f U (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    (hrange : ∀ x ∈ U,
      (chartAt (EuclideanSpace ℝ (Fin n)) b) (f x) +
        M40.chartSmoothingDisplacement (chartAt LoopPlane p)
          (chartAt (EuclideanSpace ℝ (Fin n)) b) rho f G x ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) b).target) :
    ContMDiff (𝓡 2) (𝓡 n) 1
      (M40.supportedChartSmoothing (chartAt LoopPlane p)
        (chartAt (EuclideanSpace ℝ (Fin n)) b) U rho f G) := by
  let e := chartAt LoopPlane p
  let h := chartAt (EuclideanSpace ℝ (Fin n)) b
  intro x
  by_cases hx : x ∈ U
  · have he : ContMDiffAt (𝓡 2) (𝓡 2) 1 e x :=
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) x (hUe hx)).contMDiffAt
        (e.open_source.mem_nhds (hUe hx))).of_le (by simp)
    have hh : ContMDiffAt (𝓡 n) (𝓡 n) 1 h (f x) :=
      ((contMDiffOn_chart (I := 𝓡 n) (n := ∞) (f x) (hfU hx)).contMDiffAt
        (h.open_source.mem_nhds (hfU hx))).of_le (by simp)
    have hhf := hh.comp x (hf x)
    have hGe : ContMDiffAt (𝓡 2) (𝓡 n) 1 (G ∘ e) x :=
      (hG.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contMDiff.contMDiffAt.comp x he
    have hv := hhf.add (((hrho.of_le (by simp)) x).smul (hGe.sub hhf))
    have hhi : ContMDiffAt (𝓡 n) (𝓡 n) 1 h.symm
        (h (f x) + M40.chartSmoothingDisplacement e h rho f G x) :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) _ (hrange x hx)).contMDiffAt
        (h.open_target.mem_nhds (hrange x hx))).of_le (by simp)
    apply (hhi.comp x hv).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact M40.chartPerturb_of_mem h U f _ hy
  · exact (hf x).congr_of_eventuallyEq
      (M40.supportedChartSmoothing_eventuallyEq e h U rho f G hfU
        (fun hs => hx (hsupp hs)))

theorem suC1_exists_chart_smoothing
    (g : RiemannianMetric n M) (p : UnitTwoSphere) (b : M)
    (rho : UnitTwoSphere → ℝ) (hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho)
    (hrho01 : ∀ x, rho x ∈ Icc 0 1)
    (hKe : tsupport rho ⊆ (chartAt LoopPlane p).source)
    (f : C(UnitTwoSphere, M)) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hfK : MapsTo f (tsupport rho) (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ h : C(UnitTwoSphere, M), ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
      (∀ x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt (𝓡 2) (𝓡 n) ∞ h x) ∧
      (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) ∞ f x → ContMDiffAt (𝓡 2) (𝓡 n) ∞ h x) ∧
      h.Homotopic f ∧ (∀ x, dist (h x) (f x) < epsilon) ∧
      ∀ x, |m60SphereIntrinsicEnergy g h x - m60SphereIntrinsicEnergy g f x| < eta := by
  let e := chartAt LoopPlane p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  have hc : (extChartAt (𝓡 n) b : M → EuclideanSpace ℝ (Fin n)) = c := rfl
  let U := e.source ∩ f ⁻¹' c.source
  let V := e.target ∩ e.symm ⁻¹' (f ⁻¹' c.source)
  let u := c ∘ f ∘ e.symm
  let r := rho ∘ e.symm
  have hK : IsCompact (tsupport rho) := (isClosed_tsupport rho).isCompact
  have hU : IsOpen U := e.open_source.inter (c.open_source.preimage f.continuous)
  have hUe : U ⊆ e.source := inter_subset_left
  have hsupport : tsupport rho ⊆ U := fun x hx => ⟨hKe hx, hfK hx⟩
  have hfU : MapsTo f U c.source := fun _ hx => hx.2
  have hV : IsOpen V := e.open_target.inter
    (c.open_source.preimage (f.continuous.comp (suSphereChart_smooth p).continuous))
  have hKcoord : IsCompact (e '' tsupport rho) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKe)
  have hKV : e '' tsupport rho ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨e.map_source (hKe hx), ?_⟩
    change f (e.symm (e x)) ∈ c.source
    rw [e.left_inv (hKe hx)]
    exact hfK hx
  have hu : ContDiffOn ℝ 1 u V := by
    apply ContMDiffOn.contDiffOn
    apply ((contMDiffOn_chart (I := 𝓡 n) (n := ∞)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp
      (hf.comp ((suSphereChart_smooth p).of_le (by simp))).contMDiffOn
    exact fun _ hx => hx.2
  have hr : ContDiff ℝ ∞ r := (hrho.comp (suSphereChart_smooth p)).contDiff
  have htargetImage : IsCompact ((c ∘ f) '' tsupport rho) :=
    hK.image_of_continuousOn (c.continuousOn.comp f.continuous.continuousOn hfK)
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_pos_inverse_chart_control c htargetImage
    (by rintro _ ⟨x, hx, rfl⟩; exact c.map_source (hfK hx)) hepsilon
  obtain ⟨G, hG, hGclose, hGenergy⟩ := suC1_smooth_approximation_jet_observable
    hKcoord hV hKV hu (suBlendEnergyObservable g b r u)
    (fun z hz => suBlendEnergyObservable_continuousAt g b
      ((hr.of_le (by simp)).contDiffAt)
      ((hu z (hKV hz)).contDiffAt (hV.mem_nhds (hKV hz)))
      (by rw [extChartAt_target]
          exact ⟨c.map_source (hKV hz).2, ⟨u z, rfl⟩⟩)) hdelta heta
  have hGclose' (x : UnitTwoSphere) (hx : x ∈ tsupport rho) :
      dist (G (e x)) (c (f x)) < delta := by
    simpa only [u, Function.comp_apply, e.left_inv (hKe hx)] using
      hGclose (e x) (mem_image_of_mem e hx)
  let displacement := M40.chartSmoothingDisplacement e c rho f G
  have hcontrol' (t : unitInterval) (x : UnitTwoSphere) (hx : x ∈ tsupport rho) :
      c (f x) + (t : ℝ) • displacement x ∈ c.target ∧
      dist (c.symm (c (f x) + (t : ℝ) • displacement x)) (f x) < epsilon := by
    have ht : (t : ℝ) * rho x ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg t.property.1 (hrho01 x).1,
        (mul_le_mul_of_nonneg_right t.property.2 (hrho01 x).1).trans
          (by simpa using (hrho01 x).2)⟩
    have hclose : dist (c (f x) + (t : ℝ) • displacement x) (c (f x)) < delta := by
      have hq : c (f x) + (t : ℝ) • displacement x - c (f x) =
          ((t : ℝ) * rho x) • (G (e x) - c (f x)) := by
        dsimp [displacement, M40.chartSmoothingDisplacement]
        module
      rw [dist_eq_norm, hq, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt
        (by simpa only [dist_eq_norm] using hGclose' x hx)
    have hc := hcontrol (c (f x)) (mem_image_of_mem (c ∘ f) hx) _ hclose
    rwa [c.left_inv (hfK hx)] at hc
  have hrange (t : unitInterval) (x : UnitTwoSphere) (hx : x ∈ U) :
      c (f x) + (t : ℝ) • displacement x ∈ c.target := by
    by_cases hxs : x ∈ tsupport rho
    · exact (hcontrol' t x hxs).1
    · have hr0 := image_eq_zero_of_notMem_tsupport hxs
      simpa only [displacement, M40.chartSmoothingDisplacement, hr0,
        zero_smul, smul_zero, add_zero] using c.map_source (hfU hx)
  have hrange1 (x : UnitTwoSphere) (hx : x ∈ U) : c (f x) + displacement x ∈ c.target := by
    simpa using hrange 1 x hx
  let h := M40.supportedChartSmoothing e c U rho f G
  have hh : ContMDiff (𝓡 2) (𝓡 n) 1 h :=
    suC1_supportedChartSmoothing p b hU hUe hrho hf hG hsupport hfU hrange1
  refine ⟨⟨h, hh.continuous⟩, hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact M40.contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one e c hU hUe hG
      contMDiffOn_chart contMDiffOn_chart_symm hsupport hrange1 hx
  · intro x hx
    exact M40.contMDiffAt_supportedChartSmoothing_of_contMDiffAt e c hU hUe
      hrho hG contMDiffOn_chart contMDiffOn_chart contMDiffOn_chart_symm
      hsupport hfU hrange1 hx
  · exact ⟨(M40.supportedChartSmoothingHomotopy e c hU hUe rho f G
      hrho.continuous hG.continuous hsupport hfU hrange).symm⟩
  · intro x
    by_cases hx : x ∈ tsupport rho
    · change dist (M40.chartPerturb c U f displacement x) (f x) < epsilon
      rw [M40.chartPerturb_of_mem c U f displacement (hsupport hx)]
      simpa using (hcontrol' 1 x hx).2
    · have hEq := M40.supportedChartSmoothing_eventuallyEq e c U rho f G hfU hx
      change dist (M40.supportedChartSmoothing e c U rho f G x) (f x) < epsilon
      rw [hEq.self_of_nhds, dist_self]
      exact hepsilon
  · intro x
    by_cases hx : x ∈ tsupport rho
    · have hxe := hKe hx
      have hzV : e x ∈ V := hKV (mem_image_of_mem e hx)
      have hEq : c ∘ h ∘ e.symm =ᶠ[𝓝 (e x)] M40.cutoffBlend r u G := by
        filter_upwards [hV.mem_nhds hzV] with z hz
        have hyU : e.symm z ∈ U := ⟨e.map_target hz.1, hz.2⟩
        have hcoord : M40.cutoffBlend rho (c ∘ f) (G ∘ e) (e.symm z) =
            M40.cutoffBlend r u G z := by
          simp only [M40.cutoffBlend, r, u, Function.comp_apply, e.right_inv hz.1]
        have htarget : M40.cutoffBlend r u G z ∈ c.target := by
          have ht := hrange1 (e.symm z) hyU
          dsimp [displacement, M40.chartSmoothingDisplacement] at ht
          have heq : M40.cutoffBlend r u G z =
              c (f (e.symm z)) + rho (e.symm z) • (G (e (e.symm z)) - c (f (e.symm z))) := by
            simp only [M40.cutoffBlend, r, u, Function.comp_apply, e.right_inv hz.1]
            module
          rw [heq]
          exact ht
        change c (M40.supportedChartSmoothing e c U rho f G (e.symm z)) = _
        rw [M40.supportedChartSmoothing_of_mem e c U rho f G hyU, hcoord,
          c.right_inv htarget]
      have htargeth : h x ∈ c.source := by
        change M40.chartPerturb c U f displacement x ∈ c.source
        rw [M40.chartPerturb_of_mem c U f displacement (hsupport hx)]
        exact c.map_target (hrange1 x (hsupport hx))
      have hplaneh := m60EnergyDensity_eq_chart g b
        ((hh.comp ((suSphereChart_smooth p).of_le (by simp))).mdifferentiable
          one_ne_zero (e x))
        (by change h (e.symm (e x)) ∈ (extChartAt (𝓡 n) b).source
            rw [e.left_inv hxe, extChartAt_source]
            exact htargeth)
      have hplanef := m60EnergyDensity_eq_chart g b
        ((hf.comp ((suSphereChart_smooth p).of_le (by simp))).mdifferentiable
          one_ne_zero (e x))
        (by change f (e.symm (e x)) ∈ (extChartAt (𝓡 n) b).source
            rw [e.left_inv hxe, extChartAt_source]
            exact hfK hx)
      have hder := suBlendJet_fderiv
        (hr.differentiable (by simp) (e x))
        (((hu (e x) hzV).contDiffAt (hV.mem_nhds hzV)).differentiableAt one_ne_zero)
        (hG.differentiable (by simp) (e x))
      have hnew : suBlendEnergyObservable g b r u (e x, G (e x), fderiv ℝ G (e x)) =
          m60SphereIntrinsicEnergy g h x := by
        rw [suSphereChart_energy g h hh p, e.left_inv hxe] at hplaneh
        have heqvalue : c ((h ∘ (chartAt LoopPlane p).symm) (e x)) =
            (1 - r (e x)) • u (e x) + r (e x) • G (e x) := by
          calc
            _ = M40.cutoffBlend r u G (e x) := hEq.self_of_nhds
            _ = _ := by dsimp [M40.cutoffBlend]; module
        have heqder : fderiv ℝ (c ∘ h ∘ e.symm) (e x) =
            fderiv ℝ (M40.cutoffBlend r u G) (e x) := hEq.fderiv_eq
        rw [hc] at hplaneh
        rw [heqder, hder] at hplaneh
        rw [heqvalue] at hplaneh
        unfold suBlendEnergyObservable
        rw [← hplaneh]
        exact mul_div_cancel_right₀ _ (by positivity)
      have hold : suBlendEnergyObservable g b r u (e x, u (e x), fderiv ℝ u (e x)) =
          m60SphereIntrinsicEnergy g f x := by
        rw [suBlendEnergyObservable_self]
        rw [suSphereChart_energy g f hf p, e.left_inv hxe] at hplanef
        have hd := congrArg (fun a => a / (16 / (‖e x‖ ^ 2 + 4) ^ 2)) hplanef.symm
        rw [mul_div_cancel_right₀ _
          (show (16 : ℝ) / (‖e x‖ ^ 2 + 4) ^ 2 ≠ 0 by positivity)] at hd
        simpa only [u, e, hc, Function.comp_apply] using hd
      have he := hGenergy (e x) (mem_image_of_mem e hx)
      rw [hnew, hold, Real.dist_eq] at he
      exact he
    · have hEq := M40.supportedChartSmoothing_eventuallyEq e c U rho f G hfU hx
      have hi : m60SphereIntrinsicEnergy g h x = m60SphereIntrinsicEnergy g f x := by
        dsimp only [m60SphereIntrinsicEnergy, h]
        rw [hEq.mfderiv_eq, hEq.self_of_nhds]
      change |m60SphereIntrinsicEnergy g h x - m60SphereIntrinsicEnergy g f x| < eta
      rw [hi, sub_self, abs_zero]
      exact heta

end PoincareConjecture.M60

end
