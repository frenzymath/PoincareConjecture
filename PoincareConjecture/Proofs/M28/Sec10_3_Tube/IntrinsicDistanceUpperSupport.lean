import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicDistanceEnergy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicDistanceTerminalChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Chart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

open EndpointVariation CoordinateExponential ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem deriv_chart_curve
    {β : ℝ → M} {p : M} {t : ℝ}
    (hβ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) β t)
    (hp : β t ∈ (extChartAt (𝓡 3) p).source) :
    deriv (fun s => extChartAt (𝓡 3) p (β s)) t =
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p) (β t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) β t 1) := by
  have hd := mfderiv_comp t
    (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp)) hβ
  rw [mfderiv_eq_fderiv] at hd
  have h := congrArg (fun A => A 1) hd
  have heq : ((extChartAt (𝓡 3) p) ∘ β) =
      (fun s => extChartAt (𝓡 3) p (β s)) := by
    funext s
    rfl
  rw [heq] at h
  change (fderiv ℝ (fun s => extChartAt (𝓡 3) p (β s)) t) 1 = _
  convert! h using 1

theorem exists_intrinsic_distance_upper_support_of_unit_geodesic
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {η σ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hη : g.IsGeodesicOn η (Icc 0 L))
    (hηU : MapsTo η (Icc 0 L) (U : Set M))
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η t 1) = 1)
    (hsegment : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      intrinsicEDist g (U : Set M) (η s) (η t) = ENNReal.ofReal |s - t|)
    (hσ0 : σ 0 = η L) (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 1 σ 0) :
    ∃ F : ℝ → ℝ, F 0 = L ∧
      HasDerivAt F
        (g.inner (η L) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1)
          (hσ0 ▸ mfderiv 𝓘(ℝ, ℝ) (𝓡 3) σ 0 1)) 0 ∧
      ∀ᶠ s in 𝓝 0, σ s ∈ U ∧ 0 ≤ F s ∧
        intrinsicEDist g (U : Set M) (η 0) (σ s) ≤ ENNReal.ofReal (F s) ∧
        intrinsicEDist g (U : Set M) (η 0) (σ s) ≠ ⊤ ∧
        (intrinsicEDist g (U : Set M) (η 0) (σ s)).toReal ≤ F s := by
  let c := extChartAt (𝓡 3) (η L)
  let q := fun t => c (η t)
  let v := fun s => c (σ s) - q L
  let G := g.pullbackCoefficients c.symm
  let Γ := christoffelBilinear G
  obtain ⟨a, r, ha, haL, hr, hq, hw, hv, hηchart, hσchart, hmap, hODE⟩ :=
    exists_terminal_chart_variation g U hL hη hηU hσ0 hσ
  let I := Ioo (-r) r
  let J := Ioo (a - r) (L + r)
  have h0 : (0 : ℝ) ∈ I := ⟨by linarith, hr⟩
  have hsub : Icc a L ⊆ J := by
    intro t ht
    change a - r < t ∧ t < L + r
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have horiginal : Icc a L ⊆ Icc 0 L := Icc_subset_Icc ha.le le_rfl
  have hv0 : v 0 = 0 := by simp only [v, q, hσ0, sub_self]
  have hcoeff : ContDiffOn ℝ 1 G c.target :=
    (g.contDiffOn_chartCoefficients (η L)).of_le (by simp)
  have hE := EndpointVariation.hasDerivAt_integral_density
    (G := G) (Γ := Γ) (q := q) (w := deriv q) (v := v) haL hr
    (isOpen_extChartAt_target (I := 𝓡 3) (η L)) hcoeff hq hw hv hv0
    (fun _ h => (hmap h).1)
    (fun t ht => (hODE t (hsub ht)).1)
    (fun t ht => (hODE t (hsub ht)).2)
    (fun _ _ _ _ => g.symm _ _ _)
    (fun t ht => isMetricCompatibleAt_chartCoefficients g (η L)
      (c.map_source (hηchart (hsub ht))))
    (fun t _ Y Z => christoffelBilinear_chart_symm g (η L) (q t) Y Z)
  let F : ℝ → ℝ := fun s =>
    a + ((∫ t in a..L, density G q (deriv q) v a L (s, t)) + (L - a) / 2)
  have hpos : ContDiffOn ℝ 1 (position q v a L) (I ×ˢ J) :=
    contDiffOn_position hq hv
  have hvel : ContDiffOn ℝ 1 (velocity (deriv q) v a L) (I ×ˢ J) :=
    contDiffOn_velocity hw hv
  let α : ℝ → ℝ → M := fun s => c.symm ∘ (fun t => position q v a L (s, t))
  have htime (s : ℝ) (_hs : s ∈ I) (t : ℝ) (ht : t ∈ Icc a L) :
      HasDerivAt (fun u => position q v a L (s, u))
        (velocity (deriv q) v a L (s, t)) t :=
    hasDerivAt_position_time (hODE t (hsub ht)).1
  have hα (s : ℝ) (hs : s ∈ I) :
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (α s) (Icc a L) := by
    apply (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := 1) (η L)).comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      exact hpos.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun t ht => ⟨hs, hsub ht⟩)
    · exact fun t ht => (hmap ⟨hs, hsub ht⟩).1
  have hαU (s : ℝ) (hs : s ∈ I) : MapsTo (α s) (Icc a L) (U : Set M) :=
    fun _ ht => (hmap ⟨hs, hsub ht⟩).2
  have hαa (s : ℝ) : α s a = η a := by
    change c.symm (q a + ((a - a) / (L - a)) • v s) = η a
    simp only [sub_self, zero_div, zero_smul, add_zero]
    exact c.left_inv (hηchart (hsub ⟨le_rfl, haL.le⟩))
  have hαL (s : ℝ) (hs : s ∈ I) : α s L = σ s := by
    have heq : position q v a L (s, L) = c (σ s) := by
      simp only [position, div_self (sub_ne_zero.mpr haL.ne'), one_smul, v]
      abel
    change c.symm (position q v a L (s, L)) = σ s
    rw [heq]
    exact c.left_inv (hσchart hs)
  have hsq (s : ℝ) (hs : s ∈ I) (t : ℝ) (ht : t ∈ Icc a L) :
      (g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1)) ^ 2 =
        G (position q v a L (s, t))
          (velocity (deriv q) v a L (s, t)) (velocity (deriv q) v a L (s, t)) := by
    have hf := ((contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := 1) (η L)).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) (η L)).mem_nhds
        (@hmap (s, t) ⟨hs, hsub ht⟩).1)).mdifferentiableAt one_ne_zero
    have h := g.tangentNorm_comp_sq_eq_pullback hf (htime s hs t ht).differentiableAt
    rw [(htime s hs t ht).deriv] at h
    convert! h using 1
  have hspeedcont (s : ℝ) (hs : s ∈ I) :
      ContinuousOn (fun t =>
        g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1)) (Icc a L) := by
    have hslice : ContinuousOn (fun t => position q v a L (s, t)) (Icc a L) :=
      hpos.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hs, hsub ht⟩)
    have hvslice : ContinuousOn (fun t => velocity (deriv q) v a L (s, t)) (Icc a L) :=
      hvel.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hs, hsub ht⟩)
    have hGs := hcoeff.continuousOn.comp hslice (fun t ht => (hmap ⟨hs, hsub ht⟩).1)
    apply (((hGs.clm_apply hvslice).clm_apply hvslice).sqrt).congr
    intro t ht
    change g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1) =
      Real.sqrt (G (position q v a L (s, t))
        (velocity (deriv q) v a L (s, t)) (velocity (deriv q) v a L (s, t)))
    rw [← hsq s hs t ht, Real.sqrt_sq (show 0 ≤
      g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1) from
        Real.sqrt_nonneg _)]
  have hdensity (s : ℝ) (hs : s ∈ I) (t : ℝ) (ht : t ∈ Icc a L) :
      density G q (deriv q) v a L (s, t) = (1 / 2 : ℝ) *
        (g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1)) ^ 2 := by
    rw [hsq s hs t ht]
    rfl
  have hdensity0 (t : ℝ) (ht : t ∈ Icc a L) :
      density G q (deriv q) v a L (0, t) = 1 / 2 := by
    have heq : α 0 =ᶠ[𝓝 t] η := by
      filter_upwards [isOpen_Ioo.mem_nhds (hsub ht)] with u hu
      change c.symm (q u + ((u - a) / (L - a)) • v 0) = η u
      rw [hv0, smul_zero, add_zero]
      exact c.left_inv (hηchart hu)
    rw [hdensity 0 h0 t ht, heq.mfderiv_eq, heq.self_of_nhds,
      hspeed t (horiginal ht)]
    norm_num
  have hF0 : F 0 = L := by
    change a + ((∫ t in a..L, density G q (deriv q) v a L (0, t)) + (L - a) / 2) = L
    rw [intervalIntegral.integral_congr (fun t ht =>
      hdensity0 t (by simpa only [uIcc_of_le haL.le] using ht)),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hσderiv : deriv v 0 = mfderiv (𝓡 3) (𝓡 3) c (σ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) σ 0 1) := by
    change deriv (fun s => c (σ s) - q L) 0 = _
    rw [deriv_sub_const]
    exact deriv_chart_curve (hσ.mdifferentiableAt one_ne_zero) (hσchart h0)
  have hηderiv : deriv q L = mfderiv (𝓡 3) (𝓡 3) c (η L)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1) :=
    deriv_chart_curve ((hη.contMDiffAt ⟨hL.le, le_rfl⟩).mdifferentiableAt one_ne_zero)
      (hηchart (hsub ⟨haL.le, le_rfl⟩))
  have hpair : G (q L) (deriv v 0) (deriv q L) =
      g.inner (η L) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1)
        (hσ0 ▸ mfderiv 𝓘(ℝ, ℝ) (𝓡 3) σ 0 1) := by
    rw [hσderiv, hηderiv]
    have htransport {y : M} (hy : y = η L) (V : TangentSpace (𝓡 3) y) :
        G (q L) (mfderiv (𝓡 3) (𝓡 3) c y V)
          (mfderiv (𝓡 3) (𝓡 3) c (η L)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1)) =
          g.inner (η L) (hy ▸ V) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1) := by
      subst y
      exact chartCoefficients_apply g (η L)
        (mem_extChartAt_source (I := 𝓡 3) (η L)) _ _
    exact (htransport hσ0 _).trans (g.symm _ _ _)
  have hFderiv : HasDerivAt F
      (g.inner (η L) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η L 1)
        (hσ0 ▸ mfderiv 𝓘(ℝ, ℝ) (𝓡 3) σ 0 1)) 0 := by
    rw [← hpair]
    simpa only [F, Pi.add_apply, Pi.add_def, zero_add, add_zero] using
      ((hE.add_const ((L - a) / 2)).const_add a)
  refine ⟨F, hF0, hFderiv, ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
  have hnonneg : 0 ≤ F s := by
    apply add_nonneg ha.le
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg haL.le (fun t ht => by
        rw [hdensity s hs t ht]
        positivity)
    · positivity
  have hbound := intrinsicEDist_le_ofReal_prefix_halfEnergy g U
    (hηU ⟨le_rfl, hL.le⟩) haL.le ha.le (hα s hs) (hαU s hs) (hspeedcont s hs) (by
      rw [hαa]
      simpa only [zero_sub, abs_neg, abs_of_pos ha] using
        hsegment 0 ⟨le_rfl, hL.le⟩ a ⟨ha.le, haL.le⟩)
  rw [hαL s hs] at hbound
  have henergy : (∫ t in a..L, (1 / 2 : ℝ) *
      (g.tangentNorm (α s t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (α s) t 1)) ^ 2) =
      ∫ t in a..L, density G q (deriv q) v a L (s, t) :=
    intervalIntegral.integral_congr (fun t ht =>
      (hdensity s hs t (by simpa only [uIcc_of_le haL.le] using ht)).symm)
  rw [henergy] at hbound
  change intrinsicEDist g (U : Set M) (η 0) (σ s) ≤ ENNReal.ofReal (F s) at hbound
  have hfinite : intrinsicEDist g (U : Set M) (η 0) (σ s) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  refine ⟨?_, hnonneg, hbound, hfinite, ?_⟩
  · rw [← hαL s hs]
    exact hαU s hs ⟨haL.le, le_rfl⟩
  · simpa only [ENNReal.toReal_ofReal hnonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

end PoincareConjecture.M28
