import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelSpatialSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedNormalSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialArclengthGauge
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TerminalC2SpeedJetBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TerminalCurvatureJetClosure
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem intrinsic_closed_prefix_of_half_open
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {S : ℝ} (haS : a < S) (hSb : S ≤ b)
    {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a S))
    (hi : M63IntrinsicRegularityOn F c (Ico a S)) :
    M63IntrinsicRegularityOn F c (Icc a S) ∧
      ∀ i, ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x S, m63CurvatureJet F c i S x⟩ :
          TangentBundle (𝓡 n) M)) := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 a⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  have hcopen : M63C2ShrinkingCurveOn F c (Ico a S) :=
    c2_restrict hc Ico_subset_Icc_self
  have hclose (r : ℝ) (har : a < r) (hrS : r ≤ S) :
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x S, m63CurvatureJet F c i S x⟩ :
          TangentBundle (𝓡 n) M))) ∧
      ∀ i, ContinuousOn
        (fun z : ℝ × ℝ =>
          (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
            TangentBundle (𝓡 n) M)) (univ ×ˢ Icc r S) := by
    obtain ⟨alpha, haa, har'⟩ := exists_between har
    obtain ⟨tau, hat, htr⟩ := exists_between har'
    have htS : tau < S := htr.trans_le hrS
    have haS' : alpha < S := hat.trans htS
    have halpha : alpha ∈ Icc a S := ⟨haa.le, haS'.le⟩
    let ell := ∫ x in (0 : ℝ)..curvePeriod,
      curveSpeed F (fun y _ => c y alpha) alpha x
    obtain ⟨hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
        _hshift, hpsishift, _hper, _hreg, _himm, hanchor, _hprincipal⟩ :=
      exists_c2_constant_speed_relabeling F (fun x => c x alpha) alpha
        (hc.periodic alpha halpha) (hc.spatial_regular alpha halpha)
        (hc.immersed alpha halpha)
    let d : ℝ → ℝ → M := fun x t => c (phi.symm x) t
    let v0 : ℝ := ell / curvePeriod
    have hv0 : 0 < v0 := div_pos hell Real.two_pi_pos
    have hinitial (x : ℝ) : curveSpeed F d alpha x = v0 := by
      change curveSpeed F (fun y _ => c (phi.symm y) alpha) alpha x = _
      exact hanchor x
    have hd : M63C2ShrinkingCurveOn F d (Icc alpha S) :=
      c2_restrict (c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpsipos hpsishift)
        (Icc_subset_Icc_left haa.le)
    have hsmooth (s : ℝ) (hs : s ∈ Ioo alpha S) :
        M63SmoothShrinkingCurveOn F d (Icc alpha s) := by
      have hslab : Icc alpha s ⊆ Ico a S :=
        fun t ht => ⟨haa.le.trans ht.1, ht.2.trans_lt hs.2⟩
      obtain ⟨_Q, _hQvalue, _hQ, hspace, hjets⟩ :=
        fixedLabel_embedded_path_smooth_of_constant_speed F hcopen hi haa hs.1
          hslab hpsi hpsipos hpsishift hinitial he hU heU hρ hρe
      exact c2ShrinkingCurve_smooth_of_embedded_spatial_jets F hs.1
        (c2_restrict hd (Icc_subset_Icc_right hs.2.le)) he hU heU hρ hρe
        (fun t ht => (he.comp (hspace t (Ioo_subset_Icc_self ht))).contDiff)
        (fun k => (hjets k).mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
    have hdSmooth : M63SmoothShrinkingCurveOn F d (Icc alpha S) := by
      refine ⟨hd, ?_⟩
      rw [interior_Icc]
      intro z hz
      obtain ⟨s, hzs, hsS⟩ := exists_between hz.2.2
      have hs : s ∈ Ioo alpha S := ⟨hz.2.1.trans hzs, hsS⟩
      have hzsmall : z ∈ univ ×ˢ interior (Icc alpha s) :=
        ⟨mem_univ _, by rw [interior_Icc]; exact ⟨hz.2.1, hzs⟩⟩
      exact (((hsmooth s hs).2 z hzsmall).contMDiffAt
        ((isOpen_univ.prod isOpen_interior).mem_nhds hzsmall)).contMDiffWithinAt
    let F0 := m63RestrictClosedFlow F alpha S (Icc_subset_Icc haa.le hSb) haS'
    have hd0 : M62ShrinkingCurve F0 d :=
      m63SmoothRestriction hdSmooth alpha S Subset.rfl haS'
    have hcurvCont : ContinuousOn
        (fun z : ℝ × ℝ => m62CurvatureSquared F d z.2 z.1)
        (univ ×ˢ Icc alpha S) := M62.curvatureSquared_continuousOn F0 d hd0
    have hrect : IsCompact (Icc (0 : ℝ) curvePeriod ×ˢ Icc alpha S) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨R0, hR0⟩ := hrect.bddAbove_image
      (hcurvCont.mono (prod_mono (subset_univ _) Subset.rfl))
    let R : ℝ := max R0 0
    have hR : 0 ≤ R := le_max_right _ _
    have hcurv (t : ℝ) (ht : t ∈ Ioo alpha S) (x : ℝ) :
        m62CurvatureSquared F d t x ≤ R := by
      have hp : Function.Periodic (m62CurvatureSquared F d t) curvePeriod :=
        M62.curvatureSquared_periodic F0 d hd0 ht
      obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ Real.two_pi_pos x
      rw [hxy]
      exact (hR0 ⟨(y, t), ⟨Ico_subset_Icc_self hy, Ioo_subset_Icc_self ht⟩, rfl⟩).trans
        (le_max_left _ _)
    obtain ⟨_K, _J, _m, _V, G, _J1, _J2, _hK, _hBounds, _hJ, _hm,
        _hV, hG, _hJ1, _hJ2, _hshort, _hspeed, hgrad, _htail, _hprimitive⟩ :=
      exists_terminal_speed_jet_bounds F hcompact haa.le hat htS hSb
        hsmooth hR hv0 hinitial hcurv
    have hjets : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ioo tau S, ∀ x,
        (F.metric t).tangentNorm (d x t) (m63CurvatureJet F d i t x) ≤ K := by
      intro i
      obtain ⟨C, _hC, hcap⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff F hcompact i
        haa.le haS' hSb hR (sub_pos.mpr hat)
      refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun t ht x => ?_⟩
      have hb := hcap S haS' le_rfl d hdSmooth hcurv t
        ⟨hat.trans ht.1, ht.2⟩ (sub_le_sub_right ht.1.le alpha) x
      exact Real.sqrt_le_sqrt hb
    have hgradient : ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Ioo tau S, ∀ x,
        |deriv (curveSpeed F d t) x| ≤ G :=
      ⟨G, hG, fun t ht x => hgrad t ⟨(hat.trans ht.1).le, ht.2⟩ x⟩
    obtain ⟨_eta, _heta, _hrec, hspatial, hclosed⟩ :=
      exists_terminal_embeddedCurvatureJets F hcompact haa.le hat htS hSb
        he hU heU hρ hρe hdSmooth hjets hgradient
    have hback : (fun x t => d (phi x) t) = c := by
      funext x t
      exact congrArg (fun y => c y t) (phi.symm_apply_apply x)
    have htransport (i : ℕ) (t : ℝ) (ht : t ∈ Icc tau S) (x : ℝ) :
        (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M) =
          (⟨d (phi x) t, m63CurvatureJet F d i t (phi x)⟩ :
            TangentBundle (𝓡 n) M) := by
      have ht' : t ∈ Icc alpha S := ⟨hat.le.trans ht.1, ht.2⟩
      have hjet := curvatureJet_comp F d
        ((hd.spatial_regular t ht').mdifferentiable (by norm_num))
        (hphi.differentiable (by norm_num)) hpos
        (fun y => (unitTangent_contMDiff_of_c2 F d (hd.spatial_regular t ht')
          (hd.immersed t ht') (phi y)).mdifferentiableAt (by norm_num))
        (fun k y => (hspatial k ⟨t, ht⟩ (phi y)).mdifferentiableAt (by norm_num)) i x
      calc
        _ = (⟨d (phi x) t, m63CurvatureJet F (fun y s => d (phi y) s) i t x⟩ :
            TangentBundle (𝓡 n) M) :=
          congrArg (fun f : ℝ → ℝ → M =>
            (⟨f x t, m63CurvatureJet F f i t x⟩ : TangentBundle (𝓡 n) M)) hback.symm
        _ = _ := by rw [hjet]
    refine ⟨?_, ?_⟩
    · intro i
      have hp := (hspatial i ⟨S, htS.le, le_rfl⟩).comp
        (hphi.of_le (by norm_num)).contMDiff
      exact hp.congr (fun x => htransport i S ⟨htS.le, le_rfl⟩ x)
    · intro i
      let B : ℝ × ℝ → ℝ × ℝ := fun z => (phi z.1, z.2)
      have hB : Continuous B := (hphi.continuous.comp continuous_fst).prodMk continuous_snd
      have hp := (hclosed i).comp (s := univ ×ˢ Icc tau S) (f := B)
        hB.continuousOn (fun _ hz => ⟨mem_univ _, hz.2⟩)
      have hnew : ContinuousOn
          (fun z : ℝ × ℝ =>
            (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
          (univ ×ˢ Icc tau S) :=
        hp.congr (fun z hz => htransport i z.2 hz.2 z.1)
      exact hnew.mono (prod_mono Subset.rfl (Icc_subset_Icc_left htr.le))
  refine ⟨{ interior_jets := ?_, closed_positive_jets := ?_ }, (hclose S haS le_rfl).1⟩
  · intro i
    simpa only [interior_Ico, interior_Icc] using hi.interior_jets i
  · intro r t har hrt hslab i
    have hrS : r ≤ S := (hslab ⟨le_rfl, hrt⟩).2
    have htS : t ≤ S := (hslab ⟨hrt, le_rfl⟩).2
    exact ((hclose r har hrS).2 i).mono
      (prod_mono Subset.rfl (Icc_subset_Icc_right htS))

end PoincareConjecture.M63
