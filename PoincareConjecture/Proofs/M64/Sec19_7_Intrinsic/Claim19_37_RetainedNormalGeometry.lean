import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalStrip
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_EmbeddedCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_CollarImage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointLift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_retained_normal_geometry
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (height : ℝ → ℝ),
        ContDiff ℝ ∞ e ∧ Measurable height ∧
        (∀ a, 0 < height a ∧ height a ≤ R) ∧
        (∀ a ∈ Ico (0 : ℝ) rampPeriod,
          InjOn (fun t => e !₂[a, t]) (Icc 0 (height a))) ∧
        InjOn e {z : AnnulusCoordinates |
          z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} ∧
        (∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
          x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
          (1 - delta) ^ 2 *
              (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 +
                (v 1) ^ 2) ≤
            N.metric.inner (e x) (fderiv ℝ e x v) (fderiv ℝ e x v)) ∧
        (∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
          x 1 ∈ Icc 0 (height (x 0)) → e x ∈ standardAnnulusDomain) ∧
        (∀ a ∈ Ico (0 : ℝ) rampPeriod,
          height a < R → ‖e !₂[a, height a]‖ = 2) ∧
        (∀ a ∈ Ico (0 : ℝ) rampPeriod,
          height a < R → Function.Injective (fderiv ℝ e !₂[a, height a])) := by
  let k : ℝ → ℝ := intrinsicGeodesicCurvature N.metric N.connection 1
  have hk : Continuous k :=
    m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0)
  have hbound : BddAbove (k '' Icc (0 : ℝ) rampPeriod) :=
    isCompact_Icc.bddAbove_image hk.continuousOn
  obtain ⟨A, hA⟩ := hbound
  let alpha : ℝ := max A 0
  have halpha : 0 ≤ alpha := le_max_right _ _
  have hka (a : ℝ) (ha : a ∈ Icc (0 : ℝ) rampPeriod) : k a ≤ alpha :=
    (hA ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  obtain ⟨R₀, hR₀, hR₀small, hstrip⟩ :=
    m64Intrinsic_exists_uniform_normal_strip K hdelta hdelta1 halpha
  obtain ⟨normal, u, hnormal, hu, hn, hboundary, hvelocity, hpoint⟩ :=
    hstrip N hK
  obtain ⟨normalG, uG, rG, hrG, hrGone, hnormalG, huG, hframeG, hboundaryG,
      hvelocityG, hInjG, hpropsG, hgeoG⟩ :=
    m64Intrinsic_exists_embedded_normal_collar N
  obtain ⟨height₀, hheight₀, hcontact⟩ :=
    m64Intrinsic_exists_measurable_contact_times hu.continuous hR₀
      (fun a => m64Intrinsic_inward_curve_enters_annulus
        (hboundary a) (hvelocity a) (hn a).2.2)
  have hnormal_eq (a : ℝ) : normal a = normalG a :=
    m64Intrinsic_inward_unit_normal_unique N (hn a).1 (hframeG a).1
      (hn a).2.1 (hframeG a).2.1 (hn a).2.2 (hframeG a).2.2
  let R := min R₀ rG
  have hR : 0 < R := lt_min hR₀ hrG
  have hRsmall : R < 1 / 10 := (min_le_left _ _).trans_lt hR₀small
  have hRrG : R ≤ rG := min_le_right _ _
  let height : ℝ → ℝ := fun a => min (height₀ a) R
  have hheight : Measurable height := hheight₀.min measurable_const
  have hheight_pos (a : ℝ) : 0 < height a := lt_min (hcontact a).1 hR
  have hheight_le (a : ℝ) : height a ≤ R := min_le_right _ _
  have hheight₀_le (a : ℝ) : height a ≤ height₀ a := min_le_left _ _
  let e : AnnulusCoordinates → AnnulusCoordinates := fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  have hlocal_at (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod) :
      ∃ b : ℝ, 0 < b ∧ b ≤ R₀ ∧
        (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
        u (a, b) ∈ standardAnnulusDomain ∧
        (b = R₀ ∨ ‖u (a, b)‖ = 1 ∨ ‖u (a, b)‖ = 2) ∧
        ∀ t ∈ Icc 0 b,
          (∀ v : ℝ × ℝ,
            (1 - delta) ^ 2 *
                (intrinsicBoundarySpeed N.metric 1 a ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
              N.metric.inner (u (a, t)) (fderiv ℝ u (a, t) v)
                (fderiv ℝ u (a, t) v)) ∧
          Function.Injective (fderiv ℝ u (a, t)) := by
    obtain ⟨b, S, I, hb, hbR, hS, hI, haS, hsub, hgeo, hinside, hend, hcontact', hmetric⟩ :=
      hpoint a (by simpa [k] using hka a ⟨ha.1, ha.2.le⟩)
    exact ⟨b, hb, hbR, hinside, hend, hcontact', hmetric⟩
  have hgeodesic_at (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod) :
      ∃ b : ℝ, 0 < b ∧ b ≤ R₀ ∧
        (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
        u (a, b) ∈ standardAnnulusDomain ∧
        (b = R₀ ∨ ‖u (a, b)‖ = 1 ∨ ‖u (a, b)‖ = 2) ∧
        N.metric.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) b) := by
    obtain ⟨b, S, I, hb, hbR, hS, hI, haS, hsub, hgeo, hinside, hend, hcontact', hmetric⟩ :=
      hpoint a (by simpa [k] using hka a ⟨ha.1, ha.2.le⟩)
    exact ⟨b, hb, hbR, hinside, hend, hcontact',
      fun t ht => hgeo a haS t (hsub ht)⟩
  have hsame (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod) :
      ∀ t ∈ Icc (0 : ℝ) (height a), u (a, t) = uG (a, t) := by
    obtain ⟨b, hb, hbR, hinside, hend, hcontact', hgeoS⟩ := hgeodesic_at a ha
    have hle : height a ≤ b := by
      calc height a ≤ height₀ a := hheight₀_le a
        _ = b := (m64Intrinsic_first_annulus_contact_unique hb (hcontact a).1
          hbR (hcontact a).2.1 hinside (hcontact a).2.2.1 hcontact'
          (hcontact a).2.2.2.2).symm
    have hgeoS' : N.metric.IsGeodesicOn (fun t => u (a, t))
        (Icc (0 : ℝ) (height a)) := by
      intro t ht
      exact hgeoS t ⟨ht.1, ht.2.trans hle⟩
    have hgeoG' : N.metric.IsGeodesicOn (fun t => uG (a, t))
        (Icc (0 : ℝ) (height a)) := by
      intro t ht
      exact hgeoG a ⟨ha.1, ha.2.le⟩ t
        ⟨ht.1, ht.2.trans ((hheight_le a).trans hRrG)⟩
    have hinit : u (a, 0) = uG (a, 0) := by
      rw [hboundary a, hboundaryG a]
    have hvel : deriv (fun s => extChartAt (𝓡 2) (u (a, 0)) (u (a, s))) 0 =
        deriv (fun s => extChartAt (𝓡 2) (uG (a, 0)) (uG (a, s))) 0 := by
      simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      rw [(hvelocity a).deriv, (hvelocityG a).deriv, hnormal_eq a]
    have heq := hgeoS'.eq_nhds_on_of_initial_data hgeoG'
      (convex_Icc _ _).isPreconnected (t₀ := 0)
      (show (0 : ℝ) ∈ Icc 0 (height a) from ⟨le_rfl, (hheight_pos a).le⟩)
      (u (a, 0)) (by simp) hinit hvel
    intro t ht
    exact (heq t ht).self_of_nhds
  have hglobal : InjOn e {z : AnnulusCoordinates |
      z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} := by
    intro x hx y hy hxy
    have hxy' : u (x 0, x 1) = u (y 0, y 1) := by
      simpa only [e, Matrix.cons_val_zero, Matrix.cons_val_one] using hxy
    have hxu := hsame (x 0) hx.1 (x 1) hx.2
    have hyu := hsame (y 0) hy.1 (y 1) hy.2
    have hpair : uG (x 0, x 1) = uG (y 0, y 1) := by
      calc uG (x 0, x 1) = u (x 0, x 1) := hxu.symm
        _ = u (y 0, y 1) := hxy'
        _ = uG (y 0, y 1) := hyu
    have hp := hInjG
      (show (x 0, x 1) ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc 0 rG from
        ⟨hx.1, ⟨hx.2.1, hx.2.2.trans ((hheight_le (x 0)).trans hRrG)⟩⟩)
      (show (y 0, y 1) ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc 0 rG from
        ⟨hy.1, ⟨hy.2.1, hy.2.2.trans ((hheight_le (y 0)).trans hRrG)⟩⟩) hpair
    ext i
    fin_cases i
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  have hray (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod) :
      InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)) := by
    intro s hs t ht heq
    have hp := hglobal
      (show !₂[a, s] ∈ {z : AnnulusCoordinates |
          z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} from
        ⟨ha, hs⟩)
      (show !₂[a, t] ∈ {z : AnnulusCoordinates |
          z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} from
        ⟨ha, ht⟩) heq
    exact congrArg (fun z => z 1) hp
  have hmetric (x : AnnulusCoordinates) (hx0 : x 0 ∈ Ico (0 : ℝ) rampPeriod)
      (hx1 : x 1 ∈ Icc 0 (height (x 0))) (v : AnnulusCoordinates) :
      (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e x) (fderiv ℝ e x v) (fderiv ℝ e x v) := by
    obtain ⟨b, hb, hbR, hinside, hend, hcontact', hmetric'⟩ := hlocal_at (x 0) hx0
    have heq := m64Intrinsic_first_annulus_contact_unique hb (hcontact (x 0)).1
      hbR (hcontact (x 0)).2.1 hinside (hcontact (x 0)).2.2.1
      hcontact' (hcontact (x 0)).2.2.2.2
    have hle : height (x 0) ≤ b := by
      calc height (x 0) ≤ height₀ (x 0) := hheight₀_le (x 0)
        _ = b := heq.symm
    have h := (hmetric' (x 1) ⟨hx1.1, hx1.2.trans hle⟩).1 (v 0, v 1)
    have hxcoord : !₂[x 0, x 1] = x := by
      ext i
      fin_cases i <;> rfl
    have hde : fderiv ℝ e x v =
        fderiv ℝ u (x 0, x 1) (v 0, v 1) := by
      simpa only [e, hxcoord, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (m64Intrinsic_normal_coordinate_differential
          (hu.differentiable (by simp) (x 0, x 1)) v)
    rw [hde]
    simpa only [e, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have himage (x : AnnulusCoordinates) (hx0 : x 0 ∈ Ico (0 : ℝ) rampPeriod)
      (hx1 : x 1 ∈ Icc 0 (height (x 0))) : e x ∈ standardAnnulusDomain := by
    obtain ⟨b, hb, hbR, hinside, hend, hcontact', hmetric'⟩ := hlocal_at (x 0) hx0
    have heq := m64Intrinsic_first_annulus_contact_unique hb (hcontact (x 0)).1
      hbR (hcontact (x 0)).2.1 hinside (hcontact (x 0)).2.2.1
      hcontact' (hcontact (x 0)).2.2.2.2
    have hle : height (x 0) ≤ b := by
      calc height (x 0) ≤ height₀ (x 0) := hheight₀_le (x 0)
        _ = b := heq.symm
    change u (x 0, x 1) ∈ standardAnnulusDomain
    by_cases hlt : x 1 < b
    · by_cases hz : x 1 = 0
      · rw [hz, hboundary]
        have hnorm : ‖intrinsicAnnulusBoundary 1 (x 0)‖ = 1 := by
          have hsq := m64Intrinsic_boundary_self_inner 1 (x 0)
          rw [real_inner_self_eq_norm_sq] at hsq
          nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 (x 0))]
        exact ⟨by rw [hnorm], by simpa only [hnorm] using (by norm_num : (1 : ℝ) ≤ 2)⟩
      · have hx1pos : 0 < x 1 := lt_of_le_of_ne hx1.1 (Ne.symm hz)
        exact ⟨(hinside (x 1) ⟨hx1pos, hlt⟩).1.le,
          (hinside (x 1) ⟨hx1pos, hlt⟩).2.le⟩
    · have heqt : x 1 = b := le_antisymm (hx1.2.trans hle) (le_of_not_gt hlt)
      rw [heqt]
      exact hend
  have hendreg (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod)
      (haR : height a < R) : Function.Injective (fderiv ℝ e !₂[a, height a]) := by
    obtain ⟨b, hb, hbR, hinside, hend, hcontact', hmetric'⟩ := hlocal_at a ha
    have heq := m64Intrinsic_first_annulus_contact_unique hb (hcontact a).1
      hbR (hcontact a).2.1 hinside (hcontact a).2.2.1 hcontact'
      (hcontact a).2.2.2.2
    have ht : height a ∈ Icc (0 : ℝ) b :=
      ⟨(hheight_pos a).le, by rw [heq]; exact hheight₀_le a⟩
    have hi := (hmetric' (height a) ht).2
    intro v w hvw
    have hde_v := m64Intrinsic_normal_coordinate_differential
      (hu.differentiable (by simp) (a, height a)) v
    have hde_w := m64Intrinsic_normal_coordinate_differential
      (hu.differentiable (by simp) (a, height a)) w
    have hp : (v 0, v 1) = (w 0, w 1) := by
      apply hi
      calc
        (fderiv ℝ u (a, height a)) (v 0, v 1) =
            fderiv ℝ e !₂[a, height a] v := hde_v.symm
        _ = fderiv ℝ e !₂[a, height a] w := hvw
        _ = (fderiv ℝ u (a, height a)) (w 0, w 1) := hde_w
    ext i
    fin_cases i
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  have houter (a : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod)
      (haR : height a < R) : ‖e !₂[a, height a]‖ = 2 := by
    have hheight_eq : height a = height₀ a := by
      apply min_eq_left
      by_contra hnot
      have hRle : R ≤ height₀ a := (lt_of_not_ge hnot).le
      have heqR : height a = R := min_eq_right hRle
      linarith
    have hcontact' := hcontact a
    have hltR₀ : height₀ a < R₀ := by
      rw [← hheight_eq]
      exact haR.trans_le (min_le_left _ _)
    have hnotR₀ : height₀ a ≠ R₀ := ne_of_lt hltR₀
    have hcontact12 : ‖u (a, height₀ a)‖ = 1 ∨
        ‖u (a, height₀ a)‖ = 2 := by
      rcases hcontact'.2.2.2.2 with hR0 | hnorm
      · exact False.elim (hnotR₀ hR0)
      · exact hnorm
    rcases hcontact12 with hnorm1 | hnorm2
    · have hparam := m64Intrinsic_exists_boundary_parameter hnorm1
      obtain ⟨c, hc, hceq⟩ := hparam
      have hsame_end := hsame a ha (height a)
        ⟨(hheight_pos a).le, le_rfl⟩
      have hendG : uG (a, height a) = intrinsicAnnulusBoundary 1 c := by
        calc
          uG (a, height a) = u (a, height a) := (hsame_end).symm
          _ = u (a, height₀ a) := by rw [hheight_eq]
          _ = intrinsicAnnulusBoundary 1 c := hceq
      have hboundary_eq : uG (c, 0) = intrinsicAnnulusBoundary 1 c :=
        hboundaryG c
      have hp := hInjG
        (show (a, height a) ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc 0 rG from
          ⟨ha, ⟨(hheight_pos a).le,
            (hheight_le a).trans hRrG⟩⟩)
        (show (c, 0) ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc 0 rG from
          ⟨hc, ⟨le_rfl, hrG.le⟩⟩)
        (hendG.trans hboundary_eq.symm)
      have hzero : height a = 0 := congrArg Prod.snd hp
      exact False.elim ((ne_of_gt (hheight_pos a)) hzero)
    · simpa only [e, Matrix.cons_val_zero, Matrix.cons_val_one, hheight_eq] using hnorm2
  refine ⟨R, hR, hRsmall, e, height, he, hheight, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; exact ⟨hheight_pos a, hheight_le a⟩
  · intro a ha; exact hray a ha
  · exact hglobal
  · intro x hx0 hx1 v; exact hmetric x hx0 hx1 v
  · intro x hx0 hx1; exact himage x hx0 hx1
  · intro a ha haR; exact houter a ha haR
  · intro a ha haR; exact hendreg a ha haR

theorem m64Intrinsic_retained_focusing_of_global_injective
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {height : ℝ → ℝ} {alpha kappa rho : ℝ}
    (hglobal : InjOn e {z : AnnulusCoordinates |
      z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))}) :
    ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      ∀ b ∈ Ico (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 b ≤ alpha → a < b →
        (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b),
          e !₂[a, t] = e !₂[b, s]) →
        Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  intro a ha hka b hb hkb hab hcollision
  rcases hcollision with ⟨t, ht, s, hs, hmeet⟩
  have hp := hglobal
    (show !₂[a, t] ∈ {z : AnnulusCoordinates |
        z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} from
      ⟨ha, ht⟩)
    (show !₂[b, s] ∈ {z : AnnulusCoordinates |
        z 0 ∈ Ico (0 : ℝ) rampPeriod ∧ z 1 ∈ Icc 0 (height (z 0))} from
      ⟨hb, hs⟩) hmeet
  have hab' : a = b := by
    have := congrArg (fun z : AnnulusCoordinates => z 0) hp
    simpa only [Matrix.cons_val_zero] using this
  exact False.elim ((ne_of_lt hab) hab')

end PoincareConjecture
