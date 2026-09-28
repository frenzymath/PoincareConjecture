import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.PathVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Curves.ArcLength

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

private theorem exists_isometric_arcLength_with_clock
    {X : Type*} [MetricSpace X] {γ : ℝ → X}
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hmin : eVariationOn γ (Icc (0 : ℝ) 1) = edist (γ 0) (γ 1)) :
    ∃ η : ℝ → X, ∃ c : ℝ → ℝ,
      η 0 = γ 0 ∧ η (dist (γ 0) (γ 1)) = γ 1 ∧
      ContinuousOn η (Icc 0 (dist (γ 0) (γ 1))) ∧
      η '' Icc 0 (dist (γ 0) (γ 1)) = γ '' Icc (0 : ℝ) 1 ∧
      ContinuousOn c (Icc (0 : ℝ) 1) ∧ MonotoneOn c (Icc (0 : ℝ) 1) ∧
      c 0 = 0 ∧ c 1 = dist (γ 0) (γ 1) ∧
      c '' Icc (0 : ℝ) 1 = Icc 0 (dist (γ 0) (γ 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η (c t) = γ t) ∧
      ∀ s ∈ Icc 0 (dist (γ 0) (γ 1)), ∀ t ∈ Icc 0 (dist (γ 0) (γ 1)),
        dist (η s) (η t) = |s - t| := by
  have hv : BoundedVariationOn γ (Icc (0 : ℝ) 1) := by
    rw [BoundedVariationOn, hmin]
    exact edist_ne_top _ _
  let η := naturalParameterization γ (Icc (0 : ℝ) 1) 0
  let c := variationOnFromTo γ (Icc (0 : ℝ) 1) 0
  have hc0 : c 0 = 0 := variationOnFromTo.self _ _ _
  have hc1 : c 1 = dist (γ 0) (γ 1) := by
    simp only [c, variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self,
      hmin, ← dist_edist]
  have hccont : ContinuousOn c (Icc (0 : ℝ) 1) :=
    Poincare.MetricCurves.continuousOn_cumulative_variation zero_le_one hc hv
  have hcmono : MonotoneOn c (Icc (0 : ℝ) 1) :=
    variationOnFromTo.monotoneOn hv.locallyBoundedVariationOn (by norm_num)
  have hcimage : c '' Icc (0 : ℝ) 1 = Icc 0 (dist (γ 0) (γ 1)) := by
    simpa only [hc0, hc1] using hccont.image_Icc_of_monotoneOn zero_le_one hcmono
  have hread : ∀ t ∈ Icc (0 : ℝ) 1, η (c t) = γ t := fun t ht =>
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero
      hv.locallyBoundedVariationOn (by norm_num) ht)
  have hunit : HasUnitSpeedOn η (Icc 0 (dist (γ 0) (γ 1))) := by
    rw [← hcimage]
    exact has_unit_speed_naturalParameterization γ hv.locallyBoundedVariationOn
      (by norm_num)
  have hlip : LipschitzOnWith 1 η (Icc 0 (dist (γ 0) (γ 1))) := by
    intro s hs t ht
    wlog hst : s ≤ t generalizing s t
    · simpa only [edist_comm] using this ht hs (le_of_not_ge hst)
    have hbound := eVariationOn.edist_le η
      (show s ∈ Icc 0 (dist (γ 0) (γ 1)) ∩ Icc s t from ⟨hs, le_rfl, hst⟩)
      (show t ∈ Icc 0 (dist (γ 0) (γ 1)) ∩ Icc s t from ⟨ht, hst, le_rfl⟩)
    have hvar := hunit hs ht
    simpa only [hvar, NNReal.coe_one, ENNReal.coe_one, one_mul, edist_dist,
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hbound
  have hη0 : η 0 = γ 0 := by
    simpa only [hc0] using hread 0 (by norm_num)
  have hη1 : η (dist (γ 0) (γ 1)) = γ 1 := by
    rw [← hc1]
    exact hread 1 (by norm_num)
  refine ⟨η, c, hη0, hη1, hlip.continuousOn, ?_, hccont, hcmono,
    hc0, hc1, hcimage, hread, ?_⟩
  · rw [← hcimage, image_image]
    exact image_congr hread
  · apply Poincare.MetricCurves.subsegment_dist_of_unit_lipschitz dist_nonneg hlip
    rw [hη0, hη1]

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_intrinsic_arcLength_minimizer
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) (U : Set M))
    (hmin : g.pathELength γ 0 1 = intrinsicEDist g (U : Set M) (γ 0) (γ 1))
    (hfinite : g.pathELength γ 0 1 ≠ ⊤) :
    let L := (g.pathELength γ 0 1).toReal
    ∃ η : ℝ → M, ∃ c : ℝ → ℝ,
      η 0 = γ 0 ∧ η L = γ 1 ∧ ContinuousOn η (Icc 0 L) ∧
      MapsTo η (Icc 0 L) (U : Set M) ∧
      η '' Icc 0 L = γ '' Icc (0 : ℝ) 1 ∧ IsCompact (η '' Icc 0 L) ∧
      ContinuousOn c (Icc (0 : ℝ) 1) ∧ MonotoneOn c (Icc (0 : ℝ) 1) ∧
      c 0 = 0 ∧ c 1 = L ∧ c '' Icc (0 : ℝ) 1 = Icc 0 L ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η (c t) = γ t) ∧
      ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        intrinsicEDist g (U : Set M) (η s) (η t) = ENNReal.ofReal |s - t| := by
  classical
  let gU := intrinsicOpenMetric g U
  let : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 3) U
  obtain ⟨τ, hτ, hread, hτlength⟩ :=
    exists_intrinsicOpenMetric_path_lift g U zero_le_one hγ hγU
  let K : Set U := τ '' Icc (0 : ℝ) 1
  have hprefix {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      gU.edist (τ 0) (τ t) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (gU.edist_le_pathELength_of_mem_Icc hτ ht)
    simpa only [gU, hτlength] using hfinite
  have hfiniteK (x y : K) : EDist.edist x y ≠ ⊤ := by
    obtain ⟨s, hs, hxs⟩ := x.property
    obtain ⟨t, ht, hyt⟩ := y.property
    apply ne_top_of_le_ne_top _ (edist_triangle x.val (τ 0) y.val)
    apply ENNReal.add_ne_top.mpr
    constructor
    · rw [edist_comm, ← hxs]
      exact hprefix hs
    · rw [← hyt]
      exact hprefix ht
  let : MetricSpace K := EMetricSpace.toMetricSpace hfiniteK
  let σ (t : ℝ) : K :=
    ⟨τ (projIcc 0 1 zero_le_one t),
      ⟨projIcc 0 1 zero_le_one t, (projIcc 0 1 zero_le_one t).property, rfl⟩⟩
  have hσ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (σ t).val = τ t := by
    simp only [σ, projIcc_of_mem zero_le_one ht]
  have hc : ContinuousOn σ (Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact hτ.continuousOn.domRestrict.comp continuous_projIcc
  have hvar : eVariationOn σ (Icc (0 : ℝ) 1) ≤ g.pathELength γ 0 1 := by
    rw [← hτlength]
    apply gU.eVariationOn_le_pathELength_of_edist_le hτ
    intro s hs t ht
    change gU.edist (σ s).val (σ t).val ≤ gU.edist (τ s) (τ t)
    rw [hσ hs, hσ ht]
  have hendpoint : edist (σ 0) (σ 1) = g.pathELength γ 0 1 := by
    have hread0 : (τ 0 : M) = γ 0 := hread (by norm_num)
    have hread1 : (τ 1 : M) = γ 1 := hread (by norm_num)
    change gU.edist (σ 0).val (σ 1).val = _
    rw [hσ (by norm_num), hσ (by norm_num),
      intrinsicOpenMetric_edist g U, hread0, hread1, hmin]
  have hvariation : eVariationOn σ (Icc (0 : ℝ) 1) = edist (σ 0) (σ 1) := by
    apply le_antisymm
    · simpa only [hendpoint] using hvar
    · exact eVariationOn.edist_le σ (by norm_num) (by norm_num)
  obtain ⟨η, c, hη0, hη1, hηcont, hηimage, hccont, hcmono,
    hc0, hc1, hcimage, hηread, hηdist⟩ := exists_isometric_arcLength_with_clock hc hvariation
  have hL : dist (σ 0) (σ 1) = (g.pathELength γ 0 1).toReal := by
    rw [dist_edist, hendpoint]
  rw [hL] at hη1 hηcont hηimage hc1 hcimage hηdist
  let ηM (t : ℝ) : M := ((η t).val : M)
  have hσread {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      ((σ t).val : M) = γ t := by
    rw [hσ ht]
    exact hread ht
  have himage : ηM '' Icc 0 (g.pathELength γ 0 1).toReal = γ '' Icc (0 : ℝ) 1 := by
    calc
      ηM '' Icc 0 (g.pathELength γ 0 1).toReal =
          (fun x : K => (x.val : M)) '' (η '' Icc 0 (g.pathELength γ 0 1).toReal) :=
        (Set.image_image (fun x : K => (x.val : M)) η _).symm
      _ = (fun x : K => (x.val : M)) '' (σ '' Icc (0 : ℝ) 1) := by rw [hηimage]
      _ = (fun t => ((σ t).val : M)) '' Icc (0 : ℝ) 1 := Set.image_image _ _ _
      _ = γ '' Icc (0 : ℝ) 1 := image_congr (fun t ht => hσread ht)
  refine ⟨ηM, c, ?_, ?_, ?_, ?_, himage, ?_, hccont, hcmono,
    hc0, hc1, hcimage, ?_, ?_⟩
  · exact (congrArg (fun x : K => (x.val : M)) hη0).trans (hσread (by norm_num))
  · exact (congrArg (fun x : K => (x.val : M)) hη1).trans (hσread (by norm_num))
  · exact continuous_subtype_val.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hηcont)
  · exact fun t _ => (η t).val.property
  · rw [himage]
    exact isCompact_Icc.image_of_continuousOn hγ.continuousOn
  · intro t ht
    exact (congrArg (fun x : K => (x.val : M)) (hηread t ht)).trans (hσread ht)
  · intro s hs t ht
    rw [← intrinsicOpenMetric_edist g U (η s).val (η t).val]
    change edist (η s) (η t) = _
    rw [edist_dist, hηdist s hs t ht]

end PoincareConjecture.M28
