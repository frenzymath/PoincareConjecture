import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TerminalC2FieldLimits
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TerminalC2Reconstruction
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelSpatialSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedNormalSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialArclengthGauge
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingScalars
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




theorem exists_closed_c2_endpoint_of_intrinsic_bounded_curvature
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Ico a T))
    (hi : M63IntrinsicRegularityOn F c (Ico a T))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ico a T, ∀ x, m62Curvature F c t x ≤ K) :
    ∃ d : ℝ → ℝ → M, M63C2ShrinkingCurveOn F d (Icc a T) ∧
      ∀ t ∈ Ico a T, ∀ x, d x t = c x t := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 a⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  obtain ⟨alpha, haa, haT'⟩ := exists_between haT
  obtain ⟨tau, hat, htT⟩ := exists_between haT'
  have hat' : a < tau := haa.trans hat
  have halpha : alpha ∈ Ico a T := ⟨haa.le, haT'⟩
  let ell := ∫ x in (0 : ℝ)..curvePeriod,
    curveSpeed F (fun y _ => c y alpha) alpha x
  obtain ⟨hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
      hshift, hpsishift, _hper, _hreg, _himm, hanchor, _hprincipal⟩ :=
    exists_c2_constant_speed_relabeling F (fun x => c x alpha) alpha
      (hc.periodic alpha halpha) (hc.spatial_regular alpha halpha)
      (hc.immersed alpha halpha)
  let q : ℝ → ℝ → M := fun x t => c (phi.symm x) t
  let v0 : ℝ := ell / curvePeriod
  have hv0 : 0 < v0 := div_pos hell Real.two_pi_pos
  have hinitial (x : ℝ) : curveSpeed F q alpha x = v0 := by
    change curveSpeed F (fun y _ => c (phi.symm y) alpha) alpha x = _
    exact hanchor x
  have hq : M63C2ShrinkingCurveOn F q (Ico alpha T) :=
    c2_restrict (c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpsipos hpsishift)
      (fun t ht => ⟨haa.le.trans ht.1, ht.2⟩)
  have hsmooth (s : ℝ) (hs : s ∈ Ioo alpha T) :
      M63SmoothShrinkingCurveOn F q (Icc alpha s) := by
    have hslab : Icc alpha s ⊆ Ico a T :=
      fun t ht => ⟨haa.le.trans ht.1, ht.2.trans_lt hs.2⟩
    obtain ⟨_Q, _hQvalue, _hQ, hspace, hjets⟩ :=
      fixedLabel_embedded_path_smooth_of_constant_speed F hc hi haa hs.1
        hslab hpsi hpsipos hpsishift hinitial he hU heU hρ hρe
    exact c2ShrinkingCurve_smooth_of_embedded_spatial_jets F hs.1
      (c2_restrict hq (fun t ht => ⟨ht.1, ht.2.trans_lt hs.2⟩)) he hU heU hρ hρe
      (fun t ht => (he.comp (hspace t (Ioo_subset_Icc_self ht))).contDiff)
      (fun k => (hjets k).mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
  have hqcurv (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) :
      m62CurvatureSquared F q t x ≤ K ^ 2 := by
    have htc : t ∈ Ico a T := ⟨(haa.trans ht.1).le, ht.2⟩
    have heq := curvature_comp F c
      ((hc.spatial_regular t htc).mdifferentiable (by norm_num))
      (hpsi.differentiable (by norm_num)) hpsipos
      ((unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t htc)
        (hc.immersed t htc) (phi.symm x)).mdifferentiableAt (by norm_num))
    have hkq : m62Curvature F q t x ≤ K := heq.trans_le (hcurv t htc (phi.symm x))
    rw [← M62.curvature_sq F q t x]
    exact pow_le_pow_left₀ (M62.curvature_nonneg F q t x) hkq 2
  obtain ⟨K0, _J, m, V, G, J1, J2, hK0, hBounds, _hJ, hm,
      hV, hG, hJ1, hJ2, _hshort, hspeed, hgradient, hjets, hprimitive⟩ :=
    exists_terminal_speed_jet_bounds F hcompact haa.le hat htT hTb hsmooth
      (pow_nonneg hK 2) hv0 hinitial hqcurv
  obtain ⟨r, s, h, v, g, hrep, hrange, hvlow, hfirst, hsecond, hvder⟩ :=
    exists_terminal_c2_fields F hcompact haa.le hat htT hTb he hU heU hρ hρe hsmooth
      hK0 (pow_nonneg hK 2) hm hV hG hJ1 hJ2 hBounds hqcurv hspeed hgradient hjets hprimitive
  obtain ⟨qbar, hqbar, hqagree⟩ := closed_c2_tail_of_terminal_fields F haa.le hat htT hTb
    he hU heU hρ hρe hq r s h v g hrep hrange
    (fun t z => hm.trans_le (hvlow t z)) hfirst hsecond hvder
  let w : ℝ → ℝ → M := fun x t => qbar (phi x) t
  have hw : M63C2ShrinkingCurveOn F w (Icc tau T) :=
    c2ShrinkingCurve_fixedLabel_comp F hqbar hphi hpos hshift
  have hwagree (t : ℝ) (ht : t ∈ Ico tau T) (x : ℝ) : w x t = c x t := by
    change qbar (phi x) t = c x t
    rw [hqagree t ht]
    exact congrArg (fun y => c y t) (phi.symm_apply_apply x)
  let d : ℝ → ℝ → M := fun x t => if t < T then c x t else w x t
  have hdagree (t : ℝ) (ht : t ∈ Ico a T) (x : ℝ) : d x t = c x t := by
    simp only [d, if_pos ht.2]
  have hdopen : M63C2ShrinkingCurveOn F d (Ico a T) := c2_congr hc hdagree
  have hdhead : M63C2ShrinkingCurveOn F d (Icc a tau) :=
    c2_restrict hdopen (fun t ht => ⟨ht.1, ht.2.trans_lt htT⟩)
  have hdtail : M63C2ShrinkingCurveOn F d (Icc tau T) := by
    apply c2_congr hw
    intro t ht x
    by_cases ht' : t < T
    · simp only [d, if_pos ht']
      exact (hwagree t ⟨ht.1, ht'⟩ x).symm
    · simp only [d, if_neg ht']
  have hunion : (univ ×ˢ Icc a tau : Set (ℝ × ℝ)) ∪ (univ ×ˢ Icc tau T) =
      univ ×ˢ Icc a T := by
    rw [← prod_union, Icc_union_Icc_eq_Icc hat'.le htT.le]
  refine ⟨d, ?_, hdagree⟩
  refine { domain_subset := Icc_subset_Icc le_rfl hTb
           periodic := ?_
           spatial_regular := ?_
           joint_c1 := ?_
           immersed := ?_
           continuous := ?_
           velocity_continuous := ?_
           curvature_continuous := ?_
           equation := ?_ }
  · intro t ht
    by_cases htt : t ≤ tau
    · exact hdhead.periodic t ⟨ht.1, htt⟩
    · exact hdtail.periodic t ⟨(lt_of_not_ge htt).le, ht.2⟩
  · intro t ht
    by_cases htt : t ≤ tau
    · exact hdhead.spatial_regular t ⟨ht.1, htt⟩
    · exact hdtail.spatial_regular t ⟨(lt_of_not_ge htt).le, ht.2⟩
  · simpa only [interior_Icc, interior_Ico] using hdopen.joint_c1
  · intro t ht
    by_cases htt : t ≤ tau
    · exact hdhead.immersed t ⟨ht.1, htt⟩
    · exact hdtail.immersed t ⟨(lt_of_not_ge htt).le, ht.2⟩
  · rw [← hunion]
    exact hdhead.continuous.union_of_isClosed hdtail.continuous
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)
  · rw [← hunion]
    exact hdhead.velocity_continuous.union_of_isClosed hdtail.velocity_continuous
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)
  · rw [← hunion]
    exact hdhead.curvature_continuous.union_of_isClosed hdtail.curvature_continuous
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)
  · intro t ht
    exact hdopen.equation t (by simpa only [interior_Icc, interior_Ico] using ht)

end PoincareConjecture.M63
