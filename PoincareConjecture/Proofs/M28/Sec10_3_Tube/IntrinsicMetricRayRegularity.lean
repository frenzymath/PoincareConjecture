import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricSpace
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizingGeodesicAssembly
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

omit [T2Space M] in
private theorem intrinsicEDist_univ_eq_riemannian
    (g : RiemannianMetric 3 M) (p q : M) :
    intrinsicEDist g univ p q = g.edist p q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro l hl
    obtain ⟨eta, h0, h1, heta, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hl
    have hle := intrinsicEDist_le_pathELength g zero_le_one heta
      (U := univ) (fun _ _ => mem_univ _)
    simpa only [h0, h1] using hle.trans hlength.le
  · rw [intrinsicEDist]
    apply le_sInf
    rintro l ⟨eta, heta, h0, h1, _hregion, rfl⟩
    exact Manifold.riemannianEDist_le_pathELength heta h0 h1 zero_le_one

theorem exists_geodesic_eq_intrinsic_metric_segment_real
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ {L : ℝ} {eta : ℝ → U}, 0 < L →
      ContinuousOn eta (Icc 0 L) →
      (∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
        dist (eta s) (eta t) = |s - t|) →
      ∃ zeta : ℝ → U,
        (intrinsicOpenMetric g U).IsGeodesicOn zeta (Icc 0 L) ∧
        EqOn zeta eta (Icc 0 L) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ zeta (Icc 0 L) ∧
        ∀ t ∈ Icc 0 L,
          (intrinsicOpenMetric g U).tangentNorm (zeta t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) zeta t 1) = 1 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro L eta hL heta hdist
  let gU := intrinsicOpenMetric g U
  have hedist (p q : U) : gU.edist p q = ENNReal.ofReal (dist p q) := by
    rw [intrinsicOpenMetric_edist, ← intrinsicOpenMetricSpace_edist g U hfinite,
      edist_dist]
  obtain ⟨zeta, hzeta, heq, hspeed⟩ :=
    exists_geodesic_eq_intrinsic_metric_segment gU (⊤ : TopologicalSpace.Opens U)
      hL heta (fun _ _ => mem_univ _)
      (fun s hs t ht => by
        change intrinsicEDist gU univ (eta s) (eta t) = _
        rw [intrinsicEDist_univ_eq_riemannian, hedist, hdist s hs t ht])
  refine ⟨zeta, hzeta, heq, ?_, hspeed⟩
  intro t ht
  exact (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hzeta ht).contMDiffWithinAt

theorem exists_geodesic_eq_intrinsic_unit_metric_segment
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ {L : ℝ} {mu : ℝ → U}, 0 ≤ L →
      ContinuousOn mu (Icc (0 : ℝ) 1) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (mu s) (mu t) = |s - t| * L) →
      ∃ nu : ℝ → U,
        (intrinsicOpenMetric g U).IsGeodesicOn nu (Icc 0 1) ∧
        EqOn nu mu (Icc 0 1) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ nu (Icc 0 1) := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro L mu hL hmu hdist
  let gU := intrinsicOpenMetric g U
  by_cases hL0 : L = 0
  · refine ⟨fun _ => mu 0, Conjugate.Realization.isGeodesicOn_const gU (mu 0) _,
      ?_, contMDiff_const.contMDiffOn⟩
    intro t ht
    apply dist_eq_zero.mp
    simpa only [hL0, mul_zero] using hdist 0 (by norm_num) t ht
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    let eta : ℝ → U := fun t => mu (t / L)
    have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
        t / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hL, (div_le_one hLpos).mpr ht.2⟩
    have heta : ContinuousOn eta (Icc (0 : ℝ) L) :=
      hmu.comp (continuous_id.div_const L).continuousOn
        (fun t ht => hparameter t ht)
    have hmetric : ∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
        dist (eta s) (eta t) = |s - t| := by
      intro s hs t ht
      change dist (mu (s / L)) (mu (t / L)) = _
      rw [hdist (s / L) (hparameter s hs) (t / L) (hparameter t ht),
        ← sub_div, abs_div, abs_of_pos hLpos, div_mul_cancel₀ _ hL0]
    obtain ⟨zeta, hzeta, heq, _hsmooth, _hspeed⟩ :=
      exists_geodesic_eq_intrinsic_metric_segment_real g U hfinite hLpos heta hmetric
    let nu : ℝ → U := fun s => zeta (L * s)
    have hscaled (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        L * s ∈ Icc (0 : ℝ) L :=
      ⟨mul_nonneg hL hs.1, by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs.2 hL⟩
    have hnu : gU.IsGeodesicOn nu (Icc 0 1) :=
      fun s hs => hzeta.comp_mul L s (hscaled s hs)
    refine ⟨nu, hnu, ?_, ?_⟩
    · intro s hs
      exact (heq (hscaled s hs)).trans (by
        change mu (L * s / L) = mu s
        rw [mul_div_cancel_left₀ s hL0])
    · intro s hs
      exact (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hnu hs).contMDiffWithinAt

theorem exists_geodesic_eq_intrinsic_metric_ray_prefix
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ {a : ℝ} {gamma : ℝ → U},
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) →
      ∀ {L : ℝ}, 0 < L → L < a →
        ∃ zeta : ℝ → U,
          (intrinsicOpenMetric g U).IsGeodesicOn zeta (Icc 0 L) ∧
          EqOn zeta gamma (Icc 0 L) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ zeta (Icc 0 L) ∧
          ∀ t ∈ Icc 0 L,
            (intrinsicOpenMetric g U).tangentNorm (zeta t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) zeta t 1) = 1 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro a gamma hdist L hL hLa
  let gU := intrinsicOpenMetric g U
  have hisometry : Isometry (fun t : Ico (0 : ℝ) a => gamma t.1) := by
    apply Isometry.of_dist_eq
    intro s t
    change dist (gamma s.1) (gamma t.1) = dist s.1 t.1
    simpa only [Real.dist_eq] using hdist s.1 s.2 t.1 t.2
  have hcontinuous : ContinuousOn gamma (Ico (0 : ℝ) a) :=
    continuousOn_iff_continuous_domRestrict.mpr hisometry.continuous
  have hsub : Icc (0 : ℝ) L ⊆ Ico (0 : ℝ) a :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt hLa⟩
  have hedist (p q : U) : gU.edist p q = ENNReal.ofReal (dist p q) := by
    rw [intrinsicOpenMetric_edist, ← intrinsicOpenMetricSpace_edist g U hfinite,
      edist_dist]
  obtain ⟨zeta, hzeta, heq, hspeed⟩ :=
    exists_geodesic_eq_intrinsic_metric_segment gU (⊤ : TopologicalSpace.Opens U)
      hL (hcontinuous.mono hsub) (fun _ _ => mem_univ _)
      (fun s hs t ht => by
        change intrinsicEDist gU univ (gamma s) (gamma t) = _
        rw [intrinsicEDist_univ_eq_riemannian, hedist,
          hdist s (hsub hs) t (hsub ht)])
  refine ⟨zeta, hzeta, heq, ?_, hspeed⟩
  intro t ht
  exact (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hzeta ht).contMDiffWithinAt

theorem intrinsic_metric_ray_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ {a : ℝ} {gamma : ℝ → U},
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) →
      (intrinsicOpenMetric g U).IsGeodesicOn gamma (Ioo 0 a) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma (Ioo 0 a) ∧
      ∀ t ∈ Ioo 0 a,
        (intrinsicOpenMetric g U).tangentNorm (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1) = 1 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro a gamma hdist
  let gU := intrinsicOpenMetric g U
  have hpointwise (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) a) :
      gU.IsGeodesicOn gamma {t} ∧
        gU.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1) = 1 := by
    let L := (t + a) / 2
    have hL : 0 < L := by dsimp [L]; linarith [ht.1, ht.2]
    have hLa : L < a := by dsimp [L]; linarith [ht.2]
    have htL : t < L := by dsimp [L]; linarith [ht.2]
    obtain ⟨zeta, hzeta, heq, _hsmooth, hspeed⟩ :=
      exists_geodesic_eq_intrinsic_metric_ray_prefix g U hfinite hdist hL hLa
    have hnear : gamma =ᶠ[𝓝 t] zeta := by
      filter_upwards [Ioo_mem_nhds ht.1 htL] with s hs
      exact (heq ⟨hs.1.le, hs.2.le⟩).symm
    refine ⟨?_, ?_⟩
    · intro u hu
      have hut : u = t := mem_singleton_iff.mp hu
      subst u
      obtain ⟨p, q, w, hlocal⟩ := hzeta t ⟨ht.1.le, htL.le⟩
      refine ⟨p, q, w, ?_⟩
      filter_upwards [hnear, hlocal] with s hs hlocals
      exact ⟨hs.trans hlocals.1, hlocals.2⟩
    · rw [hnear.mfderiv_eq, hnear.self_of_nhds]
      exact hspeed t ⟨ht.1.le, htL.le⟩
  have hgeodesic : gU.IsGeodesicOn gamma (Ioo 0 a) :=
    fun t ht => (hpointwise t ht).1 t (mem_singleton t)
  refine ⟨hgeodesic, ?_, fun t ht => (hpointwise t ht).2⟩
  intro t ht
  exact (Conjugate.Realization.contMDiffAt_of_isGeodesicOn
    hgeodesic ht).contMDiffWithinAt

end PoincareConjecture.M28
