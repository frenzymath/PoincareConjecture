import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRegionChart
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactGeodesicContinuation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LipschitzTangency

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_constrained_minimizer_last_contact_tangent
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b p : ℝ}
    (hinj : InjOn alpha (Icc a b)) (hp : p ∈ Ioo a b) (hregular : deriv alpha p ≠ 0)
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha p ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc a b ∪ W) (hfV : frontier V = frontier U)
    (hK : IsCompact (closure U)) {gamma : ℝ → AnnulusCoordinates} {L u : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L))
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ c ∈ Icc 0 L, ∀ d ∈ Icc 0 L, c ≤ d →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma c → tau 1 = gamma d → MapsTo tau (Icc 0 1) (closure U) →
        ENNReal.ofReal (d - c) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (hu : u ∈ Ioo 0 L) (hpoint : gamma u = alpha p)
    (hgeo : G.IsGeodesicOn gamma (Ioo u L)) :
    ∃ v : AnnulusCoordinates, HasDerivWithinAt gamma v (Ioi u) u ∧ v ≠ 0 ∧
      ∃ c : ℝ, c ≠ 0 ∧ v = c • deriv alpha p := by
  obtain ⟨v, hv⟩ := m64Intrinsic_compact_geodesic_has_right_derivative G hK hu.2 hgeo
    (fun t ht => hconf ⟨hu.1.le.trans ht.1.le, ht.2.le⟩)
    (hc.continuousAt (Icc_mem_nhds hu.1 hu.2)).continuousWithinAt
  let t := (u + L) / 2
  have ht : t ∈ Ioo u L := ⟨by dsimp only [t]; linarith [hu.2],
    by dsimp only [t]; linarith [hu.2]⟩
  have hne : gamma u ≠ gamma t := by
    intro hsame
    have hminimum := hmin u ⟨hu.1.le, hu.2.le⟩ t ⟨hu.1.le.trans ht.1.le, ht.2.le⟩
      ht.1.le (fun _ => gamma u) continuousOn_const rfl hsame (fun _ _ => hconf ⟨hu.1.le, hu.2.le⟩)
    have hlength : m64IntrinsicCurveVariation G (fun _ => gamma u) 0 1 ≤ ENNReal.ofReal 0 := by
      apply m64Intrinsic_curveVariation_le_of_edist_le G le_rfl
      intro s _ t _
      simpa only [sub_self, abs_zero, zero_mul] using hlip u ⟨hu.1.le, hu.2.le⟩ u ⟨hu.1.le, hu.2.le⟩
    have hnonpos := (ENNReal.ofReal_le_ofReal_iff (show (0 : ℝ) ≤ 0 from le_rfl)).mp
      (hminimum.trans hlength)
    linarith [ht.1]
  have hvne : v ≠ 0 := m64Intrinsic_compact_geodesic_right_derivative_ne_zero G hK hu.2
    hgeo (fun t ht => hconf ⟨hu.1.le.trans ht.1.le, ht.2.le⟩)
    (hc.continuousAt (Icc_mem_nhds hu.1 hu.2)).continuousWithinAt ht hne hv
  obtain ⟨H, h0, hbase, hH, hHi, hfront, hside⟩ :=
    m64Intrinsic_exists_arc_region_chart ha hinj hp hregular hW hpW hU hV hdisj hfU hfV
  have htarget : gamma u ∈ H.target := by rw [hpoint, ← hbase]; exact H.map_source h0
  have hDi : H.symm.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hHi.mdifferentiableOn (by simp), hH.mdifferentiableOn (by simp)⟩
  let J : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates := hDi.mfderiv htarget
  have hJ : HasFDerivAt H.symm J.toContinuousLinearMap (gamma u) := by
    change HasFDerivAt H.symm (mfderiv (𝓡 2) (𝓡 2) H.symm (gamma u)) (gamma u)
    rw [mfderiv_eq_fderiv]
    exact ((contMDiffOn_iff_contDiffOn.mp hHi _ htarget).contDiffAt
      (H.open_target.mem_nhds htarget)).differentiableAt (by simp) |>.hasFDerivAt
  have hcoordinate : HasDerivWithinAt (fun r : ℝ => H.symm (gamma (u + r)))
      (J v) (Ioi 0) 0 := by
    have hcomp := hJ.comp_hasDerivWithinAt u hv
    have hh := hcomp.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add u).hasDerivWithinAt
      (show MapsTo (fun r : ℝ => u + r) (Ioi 0) (Ioi u) from fun r hr => by
        change u < u + r
        change 0 < r at hr
        linarith)
      (by simp)
    simpa only [Function.comp_def, one_smul, id_eq] using! hh
  let P : AnnulusCoordinates →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hvanish (ell : AnnulusCoordinates →L[ℝ] ℝ)
      (hregion : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ 0 ≤ ell z) :
      ell (J v) = 0 := by
    let C := (ConvexCone.positive ℝ ℝ).comap ell.toLinearMap
    have hC : IsClosed (C : Set AnnulusCoordinates) :=
      isClosed_le continuous_const ell.continuous
    have hC0 : (0 : AnnulusCoordinates) ∈ C := by change 0 ≤ ell 0; simp
    obtain ⟨hpos, hneg⟩ := m64Intrinsic_constrained_minimizer_outgoing_tangent_mem
      G hc hconf hlip hmin H h0 hH hHi C hC hC0 hregion hu
      (hpoint.trans hbase.symm) hcoordinate
    change 0 ≤ ell (J v) at hpos
    change 0 ≤ ell (-J v) at hneg
    rw [map_neg] at hneg
    linarith
  have hJv : (J v) 1 = 0 := by
    rcases hside with hpos | hneg
    · exact hvanish P hpos
    · have hh := hvanish (-P) (by
        filter_upwards [hneg] with z hz
        change H z ∈ closure U ↔ 0 ≤ -(z 1)
        exact hz.trans neg_nonneg.symm)
      exact neg_eq_zero.mp hh
  have hJalpha : HasFDerivAt H.symm J.toContinuousLinearMap (alpha p) := hpoint ▸ hJ
  have hzero : H.symm (alpha p) = 0 := by rw [← hbase, H.left_inv h0]
  have halphaTarget : alpha p ∈ H.target := hpoint ▸ htarget
  have halimit : Tendsto (fun s : ℝ => H.symm (alpha s)) (𝓝 p)
      (𝓝 (0 : AnnulusCoordinates)) := by
    have hcont := (H.continuousAt_symm halphaTarget).comp ha.continuous.continuousAt
    simpa only [Function.comp_def, hzero] using! hcont.tendsto
  have hatarget : ∀ᶠ s in 𝓝 p, alpha s ∈ H.target :=
    ha.continuous.continuousAt.preimage_mem_nhds (H.open_target.mem_nhds halphaTarget)
  have haline : (fun s : ℝ => (H.symm (alpha s)) 1) =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [halimit.eventually hfront, hatarget, Ioo_mem_nhds hp.1 hp.2] with s hs ht hi
    apply hs.mp
    rw [H.right_inv ht, hfU]
    exact Or.inl ⟨s, Ioo_subset_Icc_self hi, rfl⟩
  have hda := hJalpha.comp_hasDerivAt p ((ha.differentiable (by simp) p).hasDerivAt)
  have hproject : HasDerivAt (fun s : ℝ => (H.symm (alpha s)) 1) (J (deriv alpha p) 1) p :=
    P.hasFDerivAt.comp_hasDerivAt p hda
  have hJa : J (deriv alpha p) 1 = 0 :=
    hproject.unique ((hasDerivAt_const p (0 : ℝ)).congr_of_eventuallyEq haline)
  have hJa0 : J (deriv alpha p) 0 ≠ 0 := by
    intro heq
    apply hregular
    apply J.injective
    rw [map_zero]
    ext i
    fin_cases i
    · exact heq
    · exact hJa
  have hmultiple : v = ((J v) 0 / J (deriv alpha p) 0) • deriv alpha p := by
    apply J.injective
    rw [map_smul]
    ext i
    fin_cases i
    · change (J v) 0 = ((J v) 0 / J (deriv alpha p) 0) * J (deriv alpha p) 0
      field_simp
    · change (J v) 1 = ((J v) 0 / J (deriv alpha p) 0) * J (deriv alpha p) 1
      rw [hJv, hJa, mul_zero]
  refine ⟨v, hv, hvne, (J v) 0 / J (deriv alpha p) 0, ?_, hmultiple⟩
  intro hzero
  exact hvne (by simpa only [hzero, zero_smul] using hmultiple)

end PoincareConjecture
