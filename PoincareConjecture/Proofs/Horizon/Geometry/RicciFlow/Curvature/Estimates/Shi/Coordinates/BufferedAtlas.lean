import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Carrier.Path
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic













set_option autoImplicit false

open Set Filter Function
open scoped Topology Manifold ContDiff Bundle ENNReal BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_shiChart_core_bounds [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ c.source) :
    IsCompact (c '' K) ∧
      ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧
        (∀ z ∈ c '' K, ∀ v : E,
          ‖v‖ ≤ L * Real.sqrt (shiChartMetric g c z v v)) ∧
        (∀ z ∈ c '' K, ‖shiChartChristoffel D c z‖ ≤ B) := by
  let H := c '' K
  have hH : IsCompact H := hK.image_of_continuousOn (hc.continuousOn.mono hKs)
  have hHt : H ⊆ c.target := by
    rintro z ⟨y, hy, rfl⟩
    exact c.map_source (hKs hy)
  let S : Set (E × E) := H ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := hH.prod (isCompact_sphere 0 1)
  have hG : ContinuousOn (fun p : E × E => shiChartMetric g c p.1) S :=
    (shiChartMetric_smooth g hc hi).continuousOn.comp continuousOn_fst
      (fun _ hp => hHt hp.1)
  have hf : ContinuousOn
      (fun p : E × E => Real.sqrt (shiChartMetric g c p.1 p.2 p.2)) S :=
    ((hG.clm_apply continuousOn_snd).clm_apply continuousOn_snd).sqrt
  have hpos (p : E × E) (hp : p ∈ S) :
      0 < Real.sqrt (shiChartMetric g c p.1 p.2 p.2) := by
    apply Real.sqrt_pos.2
    apply shiChartMetric_pos g hc hi (hHt hp.1)
    have hn : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
    intro he
    rw [he, norm_zero] at hn
    norm_num at hn
  obtain ⟨δ, hδ, hδbound⟩ := hS.exists_forall_le' hf hpos
  obtain ⟨B₀, hB₀⟩ := hH.exists_bound_of_continuousOn
    («E» := E →L[ℝ] E →L[ℝ] E) (f := shiChartChristoffel D c)
    ((shiChartChristoffel_smooth D hc hi).continuousOn.mono hHt)
  refine ⟨hH, max 1 (1 / δ), max 0 B₀, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    let w : E := (‖v‖⁻¹ : ℝ) • v
    have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    have hrep : ‖v‖ • w = v := by
      simp only [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    have hδw := hδbound (z, w) ⟨hz, mem_sphere_zero_iff_norm.mpr hw⟩
    have hdiag : shiChartMetric g c z v v =
        ‖v‖ ^ 2 * shiChartMetric g c z w w := by
      calc
        _ = shiChartMetric g c z (‖v‖ • w) (‖v‖ • w) := by rw [hrep]
        _ = _ := by
          simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
    have hroot : Real.sqrt (shiChartMetric g c z v v) =
        ‖v‖ * Real.sqrt (shiChartMetric g c z w w) := by
      rw [hdiag, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have hnorm : ‖v‖ ≤ Real.sqrt (shiChartMetric g c z v v) / δ := by
      apply (le_div_iff₀ hδ).2
      rw [hroot]
      nlinarith [mul_le_mul_of_nonneg_left hδw (norm_nonneg v)]
    calc
      ‖v‖ ≤ Real.sqrt (shiChartMetric g c z v v) / δ := hnorm
      _ = (1 / δ) * Real.sqrt (shiChartMetric g c z v v) := by ring
      _ ≤ max 1 (1 / δ) * Real.sqrt (shiChartMetric g c z v v) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  · intro z hz
    exact (hB₀ z hz).trans (le_max_right _ _)

set_option maxHeartbeats 1200000 in

theorem exists_shi_buffered_atlas [T2Space M] (D : LeviCivitaData g)
    {C : Set M} (hC : IsCompact C) :
    ∃ (m : ℕ) (c : Fin m → OpenPartialHomeomorph M E)
      (K : Fin m → Set M) (r L B : ℝ),
      0 < r ∧ r ≤ 1 ∧ 1 ≤ L ∧ 0 ≤ B ∧
      (∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source) ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target) ∧
      (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ (c i).source) ∧
      (∀ i, IsCompact ((c i) '' K i)) ∧
      (∀ y ∈ C, ∃ i, y ∈ interior (K i)) ∧
      (∀ y ∈ C, ∃ i, g.ball y r ⊆ interior (K i)) ∧
      (∀ i z, z ∈ (c i) '' K i → ∀ v : E,
        ‖v‖ ≤ L * Real.sqrt (shiChartMetric g (c i) z v v)) ∧
      (∀ i z, z ∈ (c i) '' K i → ‖shiChartChristoffel D (c i) z‖ ≤ B) := by
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hlocal (y : C) : ∃ K : Set M,
      IsCompact K ∧ (y : M) ∈ interior K ∧ K ⊆ (chartAt E (y : M)).source :=
    exists_compact_subset (chartAt E (y : M)).open_source (mem_chart_source E (y : M))
  choose K₀ hK₀ hK₀int hK₀s using hlocal
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun y : C => interior (K₀ y))
    (fun _ => isOpen_interior) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hK₀int ⟨y, hy⟩⟩)
  let e : Fin s.card ≃ s := s.equivFin.symm
  let c : Fin s.card → OpenPartialHomeomorph M E := fun i => chartAt E ((e i).1 : M)
  let K : Fin s.card → Set M := fun i => K₀ (e i).1
  have hc (i : Fin s.card) : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source :=
    contMDiffOn_chart (I := 𝓡 n)
  have hi (i : Fin s.card) : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target :=
    contMDiffOn_chart_symm (I := 𝓡 n)
  have hK (i : Fin s.card) : IsCompact (K i) := hK₀ (e i).1
  have hKs (i : Fin s.card) : K i ⊆ (c i).source := hK₀s (e i).1
  have hcover (y : M) (hy : y ∈ C) : ∃ i, y ∈ interior (K i) := by
    obtain ⟨z, hzs, hz⟩ := mem_iUnion₂.mp (hs hy)
    refine ⟨e.symm ⟨z, hzs⟩, ?_⟩
    simpa only [K, Equiv.apply_symm_apply] using hz
  have hbound (i : Fin s.card) := exists_shiChart_core_bounds D (hc i) (hi i) (hK i) (hKs i)
  choose L₀ B₀ hL₀ hB₀ hmetric₀ hGamma₀ using fun i => (hbound i).2
  let L : ℝ := 1 + ∑ i, L₀ i
  let B : ℝ := ∑ i, B₀ i
  have hsumL : 0 ≤ ∑ i, L₀ i :=
    Finset.sum_nonneg fun i _ => zero_le_one.trans (hL₀ i)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hB₀ i
  have hLi (i : Fin s.card) : L₀ i ≤ L := by
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin s.card))) => zero_le_one.trans (hL₀ j))
      (Finset.mem_univ i)
    dsimp [L]
    linarith
  have hBi (i : Fin s.card) : B₀ i ≤ B :=
    Finset.single_le_sum (fun j _ => hB₀ j) (Finset.mem_univ i)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  obtain ⟨η, hη, hηcover⟩ := lebesgue_number_lemma_of_emetric hC
    (fun i : Fin s.card => isOpen_interior (s := K i)) (by
      intro y hy
      exact mem_iUnion.mpr (hcover y hy))
  obtain ⟨r, _, hr, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  have hbuffer (y : M) (hy : y ∈ C) : ∃ i, g.ball y (min 1 r) ⊆ interior (K i) := by
    obtain ⟨i, hiη⟩ := hηcover y hy
    refine ⟨i, fun z hz => hiη ?_⟩
    apply Metric.mem_eball'.2
    change g.edist y z < η
    exact hz.trans ((ENNReal.ofReal_le_ofReal (min_le_right 1 r)).trans_lt hrη)
  refine ⟨s.card, c, K, min 1 r, L, B, lt_min zero_lt_one hrpos,
    min_le_left _ _, hL, hB, hc, hi, hK, hKs, fun i => (hbound i).1,
    hcover, hbuffer, ?_, ?_⟩
  · intro i z hz v
    exact (hmetric₀ i z hz v).trans
      (mul_le_mul_of_nonneg_right (hLi i) (Real.sqrt_nonneg _))
  · intro i z hz
    exact (hGamma₀ i z hz).trans (hBi i)

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_coordinate_velocity_metric
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    {t : ℝ} (ht : γ t ∈ c.source) :
    deriv (c ∘ γ) t = mvfderiv (𝓡 n) c (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) ∧
      Real.sqrt (shiChartMetric g c (c (γ t))
        (deriv (c ∘ γ) t) (deriv (c ∘ γ) t)) = pathSpeed g γ t := by
  have hcd := (hc.contMDiffAt (c.open_source.mem_nhds ht)).mdifferentiableAt (by simp)
  have hder : deriv (c ∘ γ) t =
      mvfderiv (𝓡 n) c (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, mvfderiv]
      using! mfderiv_comp_apply t hcd (hγ.mdifferentiableAt one_ne_zero) (1 : ℝ)
  refine ⟨hder, ?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfield : shiChartField c (deriv (c ∘ γ) t) (γ t) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 := by
    rw [hder]
    exact (shiChart_mfderiv_isInvertible hc hi ht).inverse_apply_self _
  have hmetric : shiChartMetric g c (c (γ t))
      (deriv (c ∘ γ) t) (deriv (c ∘ γ) t) =
      g.inner (γ t) (shiChartField c (deriv (c ∘ γ) t) (γ t))
        (shiChartField c (deriv (c ∘ γ) t) (γ t)) := by
    change g.inner (c.symm (c (γ t)))
      (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm (c (γ t)) (deriv (c ∘ γ) t))
      (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm (c (γ t)) (deriv (c ∘ γ) t)) = _
    rw [← shiChartField_at_inverse hc hi (c.map_source ht)]
    exact congrArg (fun y => g.inner y
      (shiChartField c (deriv (c ∘ γ) t) y) (shiChartField c (deriv (c ∘ γ) t) y))
      (c.left_inv ht)
  rw [hmetric, hfield]
  rfl

set_option maxHeartbeats 1200000 in

theorem exists_shi_common_mesh (D : LeviCivitaData g) {C : Set M} {m : ℕ}
    (c : Fin m → OpenPartialHomeomorph M E) (K : Fin m → Set M)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hKs : ∀ i, K i ⊆ (c i).source)
    {r L B R : ℝ} (hr : 0 < r) (hL : 1 ≤ L) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hbuffer : ∀ y ∈ C, ∃ i, g.ball y r ⊆ interior (K i))
    (hmetric : ∀ i z, z ∈ (c i) '' K i → ∀ v : E,
      ‖v‖ ≤ L * Real.sqrt (shiChartMetric g (c i) z v v))
    (hGamma : ∀ i z, z ∈ (c i) '' K i → ‖shiChartChristoffel D (c i) z‖ ≤ B) :
    ∃ N : ℕ, 0 < N ∧ R / (N : ℝ) < r ∧
      1 / (N : ℝ) ≤ 1 / (2 * (B * L * R) + 1) ∧
      ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ →
        MapsTo γ (Icc 0 1) C → (∀ t ∈ Icc 0 1, pathSpeed g γ t ≤ R) →
        ∃ label : Fin N → Fin m, ∀ j : Fin N,
          let a : ℝ := (j.val : ℝ) / N
          let b : ℝ := ((j.val : ℝ) + 1) / N
          MapsTo γ (Icc a b) (interior (K (label j))) ∧
          (∀ t ∈ Icc a b, ‖deriv ((c (label j)) ∘ γ) t‖ ≤ L * R) ∧
          (∀ t ∈ Icc a b,
            ‖shiChartChristoffel D (c (label j)) (c (label j) (γ t))
              (deriv ((c (label j)) ∘ γ) t)‖ ≤ B * L * R) := by
  classical
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR1 : 0 < R + 1 := by linarith
  have hden : 0 < 2 * (B * L * R) + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt
    (lt_min (div_pos hr hR1) (one_div_pos.mpr hden))
  let N := k + 1
  have hN : 0 < N := Nat.succ_pos k
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrecip : 1 / (N : ℝ) < min (r / (R + 1)) (1 / (2 * (B * L * R) + 1)) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using hk
  have hmesh : R / (N : ℝ) < r := by
    calc
      R / (N : ℝ) ≤ (R + 1) / (N : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hNreal.le
      _ < r := by
        have h := (lt_div_iff₀ hR1).mp (lt_min_iff.mp hrecip).1
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
  refine ⟨N, hN, hmesh, (lt_min_iff.mp hrecip).2.le, ?_⟩
  intro γ hγ hγC hspeed
  have hlabels (j : Fin N) : ∃ i : Fin m,
      MapsTo γ (Icc ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N)) (interior (K i)) := by
    let a : ℝ := (j.val : ℝ) / N
    let b : ℝ := ((j.val : ℝ) + 1) / N
    have hj : (j.val : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hNreal.le
    have hb1 : b ≤ 1 := (div_le_one hNreal).2 hj
    have hab : a ≤ b := div_le_div_of_nonneg_right (by linarith) hNreal.le
    have hba : b - a = 1 / (N : ℝ) := by dsimp [a, b]; ring
    obtain ⟨i, hiBall⟩ := hbuffer (γ a) (hγC ⟨ha0, hab.trans hb1⟩)
    have hint : (∫ t in a..b, pathSpeed g γ t) ≤ R * (b - a) := by
      calc
        _ ≤ ∫ _ in a..b, R := intervalIntegral.integral_mono_on hab
          ((continuous_pathSpeed g hγ).intervalIntegrable a b)
          (continuous_const.intervalIntegrable a b)
          (fun t ht => hspeed t ⟨ha0.trans ht.1, ht.2.trans hb1⟩)
        _ = R * (b - a) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
    have hshort : g.pathELength γ a b < ENNReal.ofReal r := by
      rw [pathELength_eq_ofReal_integral_pathSpeed g hγ hab]
      apply (ENNReal.ofReal_le_ofReal hint).trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff hr).2
      simpa only [hba, mul_one_div] using hmesh
    exact ⟨i, fun t ht => hiBall
      (mapsTo_ball_of_pathELength_lt g (γ a) hab hγ.contMDiffOn rfl hshort ht)⟩
  choose label hlabel using hlabels
  refine ⟨label, ?_⟩
  intro j
  dsimp only
  have hT (t : ℝ)
      (ht : t ∈ Icc ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N)) :
      ‖deriv ((c (label j)) ∘ γ) t‖ ≤ L * R := by
    have hcore : γ t ∈ K (label j) := interior_subset (hlabel j ht)
    have hsource : γ t ∈ (c (label j)).source := hKs (label j) hcore
    have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hNreal.le).trans ht.1
    have hj : (j.val : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    have ht1 : t ≤ 1 := ht.2.trans ((div_le_one hNreal).2 hj)
    calc
      _ ≤ L * Real.sqrt (shiChartMetric g (c (label j)) (c (label j) (γ t))
          (deriv ((c (label j)) ∘ γ) t) (deriv ((c (label j)) ∘ γ) t)) :=
        hmetric (label j) _ (mem_image_of_mem _ hcore) _
      _ = L * pathSpeed g γ t := by
        rw [(shiChart_coordinate_velocity_metric (hc (label j)) (hi (label j)) hγ hsource).2]
      _ ≤ L * R := mul_le_mul_of_nonneg_left (hspeed t ⟨ht0, ht1⟩) hL0
  refine ⟨hlabel j, hT, ?_⟩
  intro t ht
  have hcore : γ t ∈ K (label j) := interior_subset (hlabel j ht)
  calc
    _ ≤ ‖shiChartChristoffel D (c (label j)) (c (label j) (γ t))‖ *
        ‖deriv ((c (label j)) ∘ γ) t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * ‖deriv ((c (label j)) ∘ γ) t‖ :=
      mul_le_mul_of_nonneg_right (hGamma (label j) _ (mem_image_of_mem _ hcore)) (norm_nonneg _)
    _ ≤ B * (L * R) := mul_le_mul_of_nonneg_left (hT t ht) hB
    _ = B * L * R := by ring

end PoincareConjecture.RicciFlowAnalysis
