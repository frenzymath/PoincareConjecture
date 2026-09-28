import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaVariationalComparison
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.StrongLimit



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Uniformity
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction ENNReal

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace M60




theorem suAlpha_common_chart_patch [T2Space M]
    (f : ℕ → C(UnitTwoSphere, M)) (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto f atTop (𝓝 f0)) (p : UnitTwoSphere) :
    let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
    let s := chartAt LoopPlane p
    ∃ (e : M → EuclideanSpace ℝ (Fin n)) (r R : ℝ),
      ContMDiff (𝓡 n) (𝓡 n) ∞ e ∧ 0 < r ∧ 0 < R ∧
      Metric.closedBall (c (f0 p)) r ⊆ c.target ∧
      (∀ z ∈ Metric.closedBall (s p) R,
        f0 (s.symm z) ∈ c.source ∧ c (f0 (s.symm z)) ∈ Metric.ball (c (f0 p)) r ∧
          e =ᶠ[𝓝 (f0 (s.symm z))] c) ∧
      ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (s p) R,
        f j (s.symm z) ∈ c.source ∧ c (f j (s.symm z)) ∈ Metric.ball (c (f0 p)) r ∧
          e =ᶠ[𝓝 (f j (s.symm z))] c := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let s := chartAt LoopPlane p
  let b : SmoothBumpFunction (𝓡 n) (f0 p) := Classical.choice inferInstance
  let e : M → EuclideanSpace ℝ (Fin n) := fun x => b x • c x
  let W := interior {x : M | b x = 1} ∩ c.source
  have hW : IsOpen W := isOpen_interior.inter c.open_source
  have hbW : f0 p ∈ W := ⟨mem_interior_iff_mem_nhds.mpr b.eventuallyEq_one,
    mem_chart_source _ _⟩
  have hcb : c (f0 p) ∈ c.target := c.map_source (mem_chart_source _ _)
  have hnear : ∀ᶠ y in 𝓝 (c (f0 p)), y ∈ c.target ∧ c.symm y ∈ W := by
    have hc : ContinuousAt c.symm (c (f0 p)) := c.symm.continuousAt hcb
    have hx : c.symm (c (f0 p)) ∈ W := by rwa [c.left_inv (mem_chart_source _ _)]
    filter_upwards [c.open_target.mem_nhds hcb,
      hc.preimage_mem_nhds (hW.mem_nhds hx)] with y hy hyW
    exact ⟨hy, hyW⟩
  obtain ⟨a, ha, haB⟩ := Metric.mem_nhds_iff.mp hnear
  let r := a / 2
  have hr : 0 < r := half_pos ha
  have hball (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.closedBall (c (f0 p)) r) :
      y ∈ c.target ∧ c.symm y ∈ W :=
    haB ((Metric.mem_closedBall.mp hy).trans_lt (by dsimp [r]; linarith))
  let V := c.source ∩ c ⁻¹' Metric.ball (c (f0 p)) r
  have hV : IsOpen V := c.isOpen_inter_preimage Metric.isOpen_ball
  have hbV : f0 p ∈ V := ⟨mem_chart_source _ _, Metric.mem_ball_self hr⟩
  have hgood {x : M} (hx : x ∈ V) :
      x ∈ c.source ∧ c x ∈ Metric.ball (c (f0 p)) r ∧ e =ᶠ[𝓝 x] c := by
    have hxW : x ∈ W := by
      have h := (hball (c x) (Metric.ball_subset_closedBall hx.2)).2
      rwa [c.left_inv hx.1] at h
    refine ⟨hx.1, hx.2, ?_⟩
    filter_upwards [isOpen_interior.mem_nhds hxW.1] with y hy
    have hyb : b y = 1 := interior_subset (s := {x : M | b x = 1}) hy
    simp only [e, hyb, one_smul]
  have hst : s.target = univ := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    change (stereographic' 2 (-p)).target = univ
    simp
  have hs : Continuous s.symm := continuousOn_univ.mp (hst ▸ s.symm.continuousOn)
  have hsp : s.symm (s p) = p := s.left_inv (mem_chart_source _ _)
  have hsource : ∀ᶠ z in 𝓝 (s p), f0 (s.symm z) ∈ V := by
    have h := ((f0.continuous.comp hs).continuousAt (x := s p)).preimage_mem_nhds
      (show V ∈ 𝓝 (f0 (s.symm (s p))) by rw [hsp]; exact hV.mem_nhds hbV)
    exact h
  obtain ⟨A, hA, hAB⟩ := Metric.mem_nhds_iff.mp hsource
  let R := A / 2
  have hR : 0 < R := half_pos hA
  have hlocal : MapsTo (f0 ∘ s.symm) (Metric.closedBall (s p) R) V := by
    intro z hz
    exact hAB ((Metric.mem_closedBall.mp hz).trans_lt (by dsimp [R]; linarith))
  have htail : ∀ᶠ j in atTop, MapsTo (f j) (s.symm '' Metric.closedBall (s p) R) V :=
    hlim (ContinuousMap.eventually_mapsTo ((isCompact_closedBall _ _).image hs) hV
      (by rintro _ ⟨z, hz, rfl⟩; exact hlocal hz))
  refine ⟨e, r, R, b.contMDiff_smul contMDiffOn_chart, hr, hR,
    fun y hy => (hball y hy).1, fun z hz => hgood (hlocal hz), ?_⟩
  exact htail.mono fun j hj z hz => hgood (hj ⟨z, hz, rfl⟩)



theorem suAlpha_observed_weak_derivatives
    [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (e : M → F) (he : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ e) (p : UnitTwoSphere) (R : ℝ) :
    let S := Metric.ball ((chartAt LoopPlane p) p) R
    let u := fun j => e ∘ f j ∘ (chartAt LoopPlane p).symm
    let u0 := e ∘ f0 ∘ (chartAt LoopPlane p).symm
    ∃ (V : Fin 2 → Lp F 2 (volume.restrict S)) (k : ℕ → ℕ)
      (hd : ∀ j i, MemLp (fun z => fderiv ℝ (u j) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 (volume.restrict S)),
      StrictMono k ∧
      (∀ i, Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges
        (fun j => (hd (k j) i).toLp (fun z => fderiv ℝ (u (k j)) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i))) (V i)) ∧
      (∀ i, MemLp (fun z => V i z) (ENNReal.ofReal (2 * alpha)) (volume.restrict S)) ∧
      ∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ S → (∫ z in S, phi z • V i z) =
          -(∫ z in S, fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) • u0 z) := by
  let : UniformSpace M := uniformSpaceOfCompactR1
  dsimp only
  let S := Metric.ball ((chartAt LoopPlane p) p) R
  let u := fun j => e ∘ f j ∘ (chartAt LoopPlane p).symm
  let u0 := e ∘ f0 ∘ (chartAt LoopPlane p).symm
  let mu := volume.restrict S
  let : IsFiniteMeasure mu := ⟨by
    change volume.restrict S univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hu (j : ℕ) : ContDiff ℝ ∞ (u j) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf j).comp (suSphereChart_smooth p)))
  have hu0 : Continuous u0 := he.continuous.comp
    (f0.continuous.comp (suSphereChart_smooth p).continuous)
  obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg (e (f0 p))).trans (hA _ (mem_range_self _))
  have hmU (j : ℕ) : MemLp (u j) 2 mu :=
    MemLp.of_bound (hu j).continuous.aestronglyMeasurable A
      (Eventually.of_forall fun z => hA _ (mem_range_self _))
  have hm0 : MemLp u0 2 mu := MemLp.of_bound hu0.aestronglyMeasurable A
    (Eventually.of_forall fun z => hA _ (mem_range_self _))
  have hUnorm (j : ℕ) : ‖(hmU j).toLp (u j)‖ ≤
      (measureUnivNNReal mu : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * A := by
    apply Lp.norm_le_of_ae_bound hA0
    filter_upwards [(hmU j).coeFn_toLp] with z hz
    rw [hz]
    exact hA _ (mem_range_self _)
  obtain ⟨B, hB, hb⟩ := suSphereChart_observedLp_bound g e he
  let T := (B * C) ^ (2 : ℝ)⁻¹
  have hC0 : 0 ≤ C := (m60SphereAlphaEnergy_nonneg g alpha (f 0)).trans (hbound 0)
  have hT : 0 ≤ T := Real.rpow_nonneg (mul_nonneg hB hC0) _
  have hD (j : ℕ) : MemLp (fun z => fderiv ℝ (u j) z) 2 volume ∧
      (eLpNorm (fun z => fderiv ℝ (u j) z) 2 volume).toReal ≤ T := by
    obtain ⟨hm, hnorm, _⟩ := hb 1 le_rfl (f j) (hf j) p
    have henergy : m60SphereAlphaEnergy g 1 (f j) ≤ C := by
      rw [m60SphereAlphaEnergy_one g (f j) (hf j)]
      exact (m60SphereEnergy_le_alphaEnergy g ha (f j) (hf j)).trans (hbound j)
    simp only [mul_one, ENNReal.ofReal_ofNat, Real.rpow_one] at hm hnorm
    refine ⟨hm, hnorm.trans ?_⟩
    exact Real.rpow_le_rpow
      (mul_nonneg hB (m60SphereAlphaEnergy_nonneg g 1 (f j)))
      (mul_le_mul_of_nonneg_left henergy hB) (by norm_num)
  have hcol (j : ℕ) (i : Fin 2) (z : LoopPlane) :
      ‖fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ ‖fderiv ℝ (u j) z‖ := by
    simpa using (fderiv ℝ (u j) z).le_opNorm (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hd (j : ℕ) (i : Fin 2) : MemLp (fun z => fderiv ℝ (u j) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 mu := by
    apply ((hD j).1.restrict S).mono
      (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    exact Eventually.of_forall (hcol j i)
  have hdnorm (j : ℕ) (i : Fin 2) : ‖(hd j i).toLp (fun z => fderiv ℝ (u j) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i))‖ ≤ T := by
    rw [Lp.norm_toLp]
    apply (ENNReal.toReal_mono (hD j).1.eLpNorm_ne_top ?_).trans (hD j).2
    exact (eLpNorm_mono_ae (Eventually.of_forall (hcol j i))).trans
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  obtain ⟨v, V, k, hk, hv, hV, htest, _, _⟩ :=
    Poincare.Analysis.Sobolev.WeakCompactness.weak_w12_subsequence Metric.isOpen_ball u
      (fun j => (hu j).contDiffOn.of_le (by simp)) (EuclideanSpace.basisFun (Fin 2) ℝ)
      hmU hd hUnorm (B := 2 * T ^ 2) (fun j => by
        rw [Fin.sum_univ_two]
        have h0 := sq_le_sq₀ (norm_nonneg _) hT |>.mpr (hdnorm j 0)
        have h1 := sq_le_sq₀ (norm_nonneg _) hT |>.mpr (hdnorm j 1)
        linarith)
  have hfun : TendstoUniformly f f0 atTop := tendstoUniformlyOn_univ.mp
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim univ isCompact_univ)
  have heuc := CompactSpace.uniformContinuous_of_continuous he.continuous
  have heU := heuc.comp_tendstoUniformly hfun
  have huU : TendstoUniformly u u0 atTop := heU.comp (chartAt LoopPlane p).symm
  have hs := Poincare.Analysis.Sobolev.WeakCompactness.tendsto_toLp_of_uniformlyOn
    Metric.isOpen_ball.measurableSet hmU hm0 huU.tendstoUniformlyOn
  have hv0 := Poincare.Analysis.Sobolev.WeakCompactness.eq_of_strong_and_weak_limit
    (hs.comp hk.tendsto_atTop) hv
  have hsuper (i : Fin 2) : MemLp (fun z => V i z) (ENNReal.ofReal (2 * alpha)) mu := by
    have hap : 0 < 2 * alpha := by linarith
    apply (suWeakLp_memLp_of_power_bound (show 1 ≤ 2 * alpha by linarith)
      (mul_nonneg (Real.rpow_nonneg hB alpha) hC0) (hV i) ?_).1
    intro j
    obtain ⟨hmem, _, hpower⟩ := hb alpha ha (f (k j)) (hf (k j)) p
    have hint : Integrable (fun z => ‖fderiv ℝ (u (k j)) z‖ ^ (2 * alpha)) volume := by
      have hi := (integrable_norm_rpow_iff hmem.1
        (ENNReal.ofReal_pos.mpr hap).ne' ENNReal.ofReal_ne_top).mpr hmem
      simpa only [ENNReal.toReal_ofReal hap.le] using hi
    calc
      (∫⁻ z, ENNReal.ofReal (‖(hd (k j) i).toLp
          (fun z => fderiv ℝ (u (k j)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) z‖ ^
            (2 * alpha)) ∂mu) =
          ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ (u (k j)) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ (2 * alpha)) ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [(hd (k j) i).coeFn_toLp] with z hz
        rw [hz]
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ (u (k j)) z‖ ^ (2 * alpha)) ∂mu :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (norm_nonneg _) (hcol (k j) i z) hap.le)
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ (u (k j)) z‖ ^ (2 * alpha)) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (∫ z, ‖fderiv ℝ (u (k j)) z‖ ^ (2 * alpha)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (B ^ alpha * C) := ENNReal.ofReal_le_ofReal
        (hpower.trans (mul_le_mul_of_nonneg_left (hbound (k j)) (Real.rpow_nonneg hB _)))
  refine ⟨V, k, hd, hk, hV, hsuper, fun i phi hphi hc hsub => ?_⟩
  rw [htest i phi hphi hc hsub, hv0]
  congr 1
  apply integral_congr_ae
  filter_upwards [hm0.coeFn_toLp] with z hz
  rw [hz]




theorem suAlpha_coordinate_weak_derivatives
    [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) (p : UnitTwoSphere) :
    let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
    let s := chartAt LoopPlane p
    ∃ R : ℝ, 0 < R ∧ MapsTo (f0 ∘ s.symm) (Metric.closedBall (s p) R) c.source ∧
      MemLp (c ∘ f0 ∘ s.symm) (ENNReal.ofReal (2 * alpha))
        (volume.restrict (Metric.ball (s p) R)) ∧
      ∃ V : Fin 2 → Lp (EuclideanSpace ℝ (Fin n)) 2
          (volume.restrict (Metric.ball (s p) R)),
        (∀ i, MemLp (fun z => V i z) (ENNReal.ofReal (2 * alpha))
          (volume.restrict (Metric.ball (s p) R))) ∧
        ∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
          tsupport phi ⊆ Metric.ball (s p) R →
          (∫ z in Metric.ball (s p) R, phi z • V i z) =
            -(∫ z in Metric.ball (s p) R,
              fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) • c (f0 (s.symm z))) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let s := chartAt LoopPlane p
  obtain ⟨e, _, R, he, _, hR, _, hlocal, _⟩ :=
    suAlpha_common_chart_patch (n := n) (fun j => ⟨f j, (hf j).continuous⟩) f0 hlim p
  have hs : Continuous s.symm := (suSphereChart_smooth p).continuous
  have hclosed (z : LoopPlane) (hz : z ∈ Metric.closedBall (s p) R) :
      e (f0 (s.symm z)) = c (f0 (s.symm z)) ∧ f0 (s.symm z) ∈ c.source :=
    ⟨(hlocal z hz).2.2.self_of_nhds, (hlocal z hz).1⟩
  obtain ⟨V, _, _, _, _, hVp, htest⟩ :=
    suAlpha_observed_weak_derivatives g ha f hf hbound f0 hlim e he p R
  refine ⟨R, hR, fun z hz => (hclosed z hz).2, ?_, V, hVp, ?_⟩
  · let mu := volume.restrict (Metric.ball (s p) R)
    let : IsFiniteMeasure mu := ⟨by
      change volume.restrict (Metric.ball (s p) R) univ < ⊤
      rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top⟩
    obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
    have hm : MemLp (e ∘ f0 ∘ s.symm) (ENNReal.ofReal (2 * alpha)) mu :=
      MemLp.of_bound (he.continuous.comp (f0.continuous.comp hs)).aestronglyMeasurable A
        (Eventually.of_forall fun z => hA _ (mem_range_self _))
    apply hm.ae_eq
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact (hclosed z (Metric.ball_subset_closedBall hz)).1
  · intro i phi hphi hc hsub
    rw [htest i phi hphi hc hsub]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    change _ • e (f0 (s.symm z)) = _
    rw [(hclosed z (Metric.ball_subset_closedBall hz)).1]

end M60

end PoincareConjecture
