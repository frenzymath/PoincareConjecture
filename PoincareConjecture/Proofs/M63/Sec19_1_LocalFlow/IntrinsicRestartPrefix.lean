import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicClosedPrefix
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedSmoothSpatialJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothLocalExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicRegularityFromSpatialLimits
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2SpeedPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_larger_intrinsic_closed_prefix
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {S T : ℝ} (haS : a < S) (hST : S < T) (hTb : T ≤ b)
    {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a T))
    (hi : M63IntrinsicRegularityOn F c (Icc a S)) :
    ∃ S' : ℝ, S < S' ∧ S' ≤ T ∧ M63IntrinsicRegularityOn F c (Icc a S') := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 a⟩
  have hcS := c2_restrict hc (Icc_subset_Icc_right hST.le)
  have hiOpen : M63IntrinsicRegularityOn F c (Ico a S) :=
    { interior_jets := fun i => by
        simpa only [interior_Icc, interior_Ico] using hi.interior_jets i
      closed_positive_jets := fun r s har hrs hsub i =>
        hi.closed_positive_jets r s har hrs (hsub.trans Ico_subset_Icc_self) i }
  have hterminal := (intrinsic_closed_prefix_of_half_open F hcompact haS
    (hST.le.trans hTb) hcS hiOpen).2
  have hleftSpatial (i : ℕ) (t : ℝ) (hat : a < t) (htS : t ≤ S) :
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M)) := by
    rcases htS.eq_or_lt with rfl | htS
    · exact hterminal i
    · exact (hi.interior_jets i).comp_contMDiff
        (contDiff_id.prodMk contDiff_const).contMDiff
        (fun _ => ⟨mem_univ _, by rw [interior_Icc]; exact ⟨hat, htS⟩⟩)
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  obtain ⟨alpha, haa, haS'⟩ := exists_between haS
  have halpha : alpha ∈ Icc a S := ⟨haa.le, haS'.le⟩
  obtain ⟨_hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
      hshift, hpsishift, _hperiod, _hregular, _himm, hanchor, _hprincipal⟩ :=
    exists_c2_constant_speed_relabeling F (fun x => c x alpha) alpha
      (hcS.periodic alpha halpha) (hcS.spatial_regular alpha halpha)
      (hcS.immersed alpha halpha)
  let d : ℝ → ℝ → M := fun x t => c (phi.symm x) t
  have hd : M63C2ShrinkingCurveOn F d (Icc a T) :=
    c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpsipos hpsishift
  have hinitial (x : ℝ) : curveSpeed F d alpha x =
      (∫ y in (0 : ℝ)..curvePeriod, curveSpeed F (fun z _ => c z alpha) alpha y) /
        curvePeriod := hanchor x
  obtain ⟨_Q, _hQvalue, _hQ, hslice, _hjets⟩ :=
    fixedLabel_embedded_path_smooth_of_constant_speed F hcS hi haa haS'
      (Icc_subset_Icc_left haa.le) hpsi hpsipos hpsishift hinitial he hU heU hρ hρe
  have hS : S ∈ Icc a T := ⟨haS.le, hST.le⟩
  let FS := m63RestrictClosedFlow F S b (Icc_subset_Icc_left haS.le) (hST.trans_le hTb)
  obtain ⟨Tq, hSTq, _hTqb, q, hq, hqinitial, hqi, hqjoint⟩ :=
    exists_smooth_local_curve_of_retraction FS he hU heU hρ hρe (fun x => d x S)
      (hd.periodic S hS) (hslice S ⟨haS'.le, le_rfl⟩) (hd.immersed S hS)
  let R : ℝ := min T Tq
  have hSR : S < R := lt_min hST hSTq
  have hRT : R ≤ T := min_le_left _ _
  have hRTq : R ≤ Tq := min_le_right _ _
  have hright : Icc S R ⊆ Icc a T :=
    fun t ht => ⟨haS.le.trans ht.1, ht.2.trans hRT⟩
  have hqr := c2_restrict hq.1 (Icc_subset_Icc_right hRTq)
  have hqF : M63C2ShrinkingCurveOn F q (Icc S R) :=
    { domain_subset := fun t ht => ⟨haS.le.trans ht.1, ht.2.trans (hRT.trans hTb)⟩
      periodic := hqr.periodic
      spatial_regular := hqr.spatial_regular
      joint_c1 := hqr.joint_c1
      immersed := hqr.immersed
      continuous := hqr.continuous
      velocity_continuous := hqr.velocity_continuous
      curvature_continuous := hqr.curvature_continuous
      equation := hqr.equation }
  have hqjets := c2ShrinkingCurve_closed_spatial_jets_of_joint_smooth F haS hSR
    he hU heU hρ hρe hqF
    (hqjoint.mono (prod_mono Subset.rfl (Icc_subset_Icc_right hRTq)))
  have hqd := c2ShrinkingCurve_unique_closed F hcompact hqF (c2_restrict hd hright)
    hqinitial
  let f : ℝ → ℝ → M := fun x t => q (phi x) t
  have hf : M63C2ShrinkingCurveOn F f (Icc S R) :=
    c2ShrinkingCurve_fixedLabel_comp F hqF hphi hpos hshift
  have hcf (t : ℝ) (ht : t ∈ Icc S R) (x : ℝ) : c x t = f x t := by
    change c x t = q (phi x) t
    rw [hqd t ht (phi x)]
    change c x t = c (phi.symm (phi x)) t
    rw [phi.symm_apply_apply]
  have freeze (g : ℝ → ℝ → M) (i : ℕ) (t : ℝ) :
      (fun x => m63CurvatureJet F g i t x) =
        (fun x => m63CurvatureJet F (fun y _ => g y t) i t x) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      funext x
      change m62SpatialDerivative F g t (fun y => m63CurvatureJet F g i t y) x =
        m62SpatialDerivative F (fun y _ => g y t) t
          (fun y => m63CurvatureJet F (fun z _ => g z t) i t y) x
      rw [ih]
      rfl
  have bundleFreeze (g : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) :
      (⟨g x t, m63CurvatureJet F g i t x⟩ : TangentBundle (𝓡 n) M) =
        (⟨g x t, m63CurvatureJet F (fun y _ => g y t) i t x⟩ :
          TangentBundle (𝓡 n) M) := by rw [congrFun (freeze g i t) x]
  have hcfJet (i : ℕ) (t : ℝ) (ht : t ∈ Icc S R) (x : ℝ) :
      (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M) =
        (⟨f x t, m63CurvatureJet F f i t x⟩ : TangentBundle (𝓡 n) M) :=
    (bundleFreeze c i t x).trans
      ((congrArg (fun gamma : ℝ → M =>
        (⟨gamma x, m63CurvatureJet F (fun y _ => gamma y) i t x⟩ :
          TangentBundle (𝓡 n) M)) (funext (hcf t ht))).trans
            (bundleFreeze f i t x).symm)
  have htransport (i : ℕ) (t : ℝ) (ht : t ∈ Icc S R) (x : ℝ) :
      (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M) =
        (⟨q (phi x) t, m63CurvatureJet F q i t (phi x)⟩ :
          TangentBundle (𝓡 n) M) := by
    rw [hcfJet i t ht x]
    have hj := curvatureJet_comp F q
      ((hqF.spatial_regular t ht).mdifferentiable (by norm_num))
      (hphi.differentiable (by norm_num)) hpos
      (fun y => (unitTangent_contMDiff_of_c2 F q (hqF.spatial_regular t ht)
        (hqF.immersed t ht) (phi y)).mdifferentiableAt (by norm_num))
      (fun k y => (hqjets.1 k ⟨t, ht⟩ (phi y)).mdifferentiableAt (by norm_num)) i x
    change (⟨q (phi x) t, m63CurvatureJet F (fun y s => q (phi y) s) i t x⟩ :
      TangentBundle (𝓡 n) M) = _
    rw [hj]
  have hrightSpatial (i : ℕ) (t : ℝ) (ht : t ∈ Icc S R) :
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M)) :=
    ((hqjets.1 i ⟨t, ht⟩).comp (hphi.of_le (by norm_num)).contMDiff).congr
      (fun x => htransport i t ht x)
  have hrightClosed (i : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Icc S R) := by
    let B : ℝ × ℝ → ℝ × ℝ := fun z => (phi z.1, z.2)
    have hB : Continuous B := (hphi.continuous.comp continuous_fst).prodMk continuous_snd
    exact ((hqjets.2 i).comp (s := univ ×ˢ Icc S R) (f := B)
      hB.continuousOn (fun _ hz => ⟨mem_univ _, hz.2⟩)).congr
        (fun z hz => htransport i z.2 hz.2 z.1)
  have hrightH : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ interior (Icc S R)) := by
    have hqH : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun z : ℝ × ℝ =>
          (⟨q z.1 z.2, m62CurvatureVector F q z.2 z.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ interior (Icc S R)) :=
      (hqi.interior_jets 0).mono
        (prod_mono Subset.rfl (interior_mono (Icc_subset_Icc_right hRTq)))
    exact (c2ShrinkingCurve_fixedLabel_curvature_contMDiffOn F hqF hphi hpos hqH).congr
      (fun z hz => hcfJet 0 z.2 (interior_subset hz.2) z.1)
  have hspatial (i : ℕ) (t : ℝ) (hat : a < t) (htR : t ≤ R) :
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M)) := by
    by_cases htS : t ≤ S
    · exact hleftSpatial i t hat htS
    · exact hrightSpatial i t ⟨(lt_of_not_ge htS).le, htR⟩
  have hclosed (r t : ℝ) (har : a < r) (hrt : r ≤ t) (htR : t ≤ R) (i : ℕ) :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Icc r t) := by
    by_cases htS : t ≤ S
    · exact hi.closed_positive_jets r t har hrt
        (fun u hu => ⟨har.le.trans hu.1, hu.2.trans htS⟩) i
    by_cases hSr : S ≤ r
    · exact (hrightClosed i).mono (prod_mono Subset.rfl (Icc_subset_Icc hSr htR))
    have hrS : r ≤ S := (lt_of_not_ge hSr).le
    have hSt : S ≤ t := (lt_of_not_ge htS).le
    have hl := hi.closed_positive_jets r S har hrS (Icc_subset_Icc_left har.le) i
    have hr := (hrightClosed i).mono (prod_mono Subset.rfl (Icc_subset_Icc_right htR))
    have hu := hl.union_of_isClosed hr (isClosed_univ.prod isClosed_Icc)
      (isClosed_univ.prod isClosed_Icc)
    apply hu.mono
    intro z hz
    by_cases hzS : z.2 ≤ S
    · exact Or.inl ⟨mem_univ _, hz.2.1, hzS⟩
    · exact Or.inr ⟨mem_univ _, (lt_of_not_ge hzS).le, hz.2.2⟩
  have hcRight := c2_restrict hc hright
  have leftSpeed (r t : ℝ) (har : a ≤ r) (hrt : r ≤ t) (htS : t ≤ S) (x : ℝ) :
      curveSpeed F c t x = curveSpeed F c r x * Real.exp
        (-∫ u in r..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x) :=
    c2ShrinkingCurve_speed_eq_exp_integral F hcS (hi.interior_jets 0) hrt
      (Icc_subset_Icc har htS) x
  have rightSpeed (r t : ℝ) (hSr : S ≤ r) (hrt : r ≤ t) (htR : t ≤ R) (x : ℝ) :
      curveSpeed F c t x = curveSpeed F c r x * Real.exp
        (-∫ u in r..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x) :=
    c2ShrinkingCurve_speed_eq_exp_integral F hcRight hrightH hrt
      (Icc_subset_Icc hSr htR) x
  have hcR := c2_restrict hc (Icc_subset_Icc_right hRT)
  have hspeed (r t : ℝ) (har : a < r) (hrt : r ≤ t) (htR : t ≤ R) (x : ℝ) :
      curveSpeed F c t x = curveSpeed F c r x * Real.exp
        (-∫ u in r..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x) := by
    by_cases htS : t ≤ S
    · exact leftSpeed r t har.le hrt htS x
    by_cases hSr : S ≤ r
    · exact rightSpeed r t hSr hrt htR x
    have hrS : r ≤ S := (lt_of_not_ge hSr).le
    have hSt : S ≤ t := (lt_of_not_ge htS).le
    have hA := (c2ShrinkingCurve_speed_normalization_continuousOn F hcR).2
    have hAleft : ContinuousOn
        (fun u => m62TangentRicci F c u x + m62CurvatureSquared F c u x) (Icc r S) :=
      hA.comp (s := Icc r S) (f := fun u : ℝ => (x, u))
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hu => ⟨mem_univ _, har.le.trans hu.1, hu.2.trans hSR.le⟩)
    have hAright : ContinuousOn
        (fun u => m62TangentRicci F c u x + m62CurvatureSquared F c u x) (Icc S t) :=
      hA.comp (s := Icc S t) (f := fun u : ℝ => (x, u))
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hu => ⟨mem_univ _, haS.le.trans hu.1, hu.2.trans htR⟩)
    have hint := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (ContinuousOn.intervalIntegrable_of_Icc hrS hAleft)
      (ContinuousOn.intervalIntegrable_of_Icc hSt hAright)
    rw [rightSpeed S t le_rfl hSt htR x, leftSpeed r S har.le hrS le_rfl x,
      mul_assoc, ← Real.exp_add, ← neg_add, hint]
  exact ⟨R, hSR, hRT, intrinsic_regularity_of_spatial_jets_and_speed_primitive F
    (haS.trans hSR) hcR he hU heU hρ hρe hspatial hclosed hspeed⟩

end PoincareConjecture.M63
