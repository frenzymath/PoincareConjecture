import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedBilinearSpatialJets
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCoefficientLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.BackwardMetricComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.MixedBounds
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricComparison
import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in

theorem generalized_stage_coefficients_and_closed_bounds
    {S : GeneralizedBlowupSequence.{u}} {T tau : ℝ} (hT : 0 < T)
    (hTtau : T < tau)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (Y : TopologicalSpace.Opens G.limit.carrier.carrier) (N : ℕ)
    (P : ℕ → RicciFlow 3 Y (Icc (-tau) 0))
    (hstage : ∀ k, (Y : Set G.limit.carrier.carrier) ⊆
      G.exhaustion.space (k + N))
    (hmetric : ∀ k s (_hs : s ∈ Icc (-tau) 0)
        (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
        (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric s).inner x v w =
        (G.embedding (k + N)).pullbackInner s hsG x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Y → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Y → G.limit.carrier.carrier) x w))
    (hcurv : ∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ k t,
      t ∈ Icc (-tau) 0 → ∀ x : Y,
        ((P k).connection t).curvatureDerivativeNorm m x ≤ D)
    (q : G.limit.carrier.carrier) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : IsOpen U) (hUc : U ⊆ (extChartAt (𝓡 3) q).target)
    (psi : EuclideanSpace ℝ (Fin 3) → Y)
    (hpsi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ psi U)
    (hpsival : ∀ x ∈ U, (psi x).val = (extChartAt (𝓡 3) q).symm x)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) psi x).IsInvertible) :
    (∀ k s (_hs : s ∈ Icc (-tau) 0)
        (_hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0),
      EqOn (((P k).metric s).pullbackCoefficients psi)
        (fun x => generalizedPullbackCoefficients G (k + N) q (s, x)) U) ∧
    (∀ r : ℕ, ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)),
      IsCompact K → K ⊆ Ioc (-T) 0 ×ˢ U →
        TendstoUniformlyOn
          (fun k z => iteratedFDeriv ℝ r
            (((P k).metric z.1).pullbackCoefficients psi) z.2)
          (fun z => iteratedFDeriv ℝ r
            ((G.limit.flow.metric z.1).pullbackCoefficients
              (extChartAt (𝓡 3) q).symm) z.2) atTop K) ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K → K ⊆ U →
      ∃ alpha beta : ℝ, 0 < alpha ∧ 0 ≤ beta ∧
        (∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K, ∀ v,
          alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients psi x v v ∧
            ((P k).metric t).pullbackCoefficients psi x v v ≤ beta * ‖v‖ ^ 2) ∧
        ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
          ∀ z ∈ Icc (-tau) 0 ×ˢ K,
            ‖iteratedFDerivWithin ℝ m
              (fun z => ((P k).metric z.1).pullbackCoefficients psi z.2)
              (Icc (-tau) 0 ×ˢ U) z‖ ≤ B := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  have htau : 0 < tau := hT.trans hTtau
  have hpsi_at {x : E} (hx : x ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ psi x :=
    (hpsi x hx).contMDiffAt (hU.mem_nhds hx)
  have hcoeff_eq : ∀ k s (hs : s ∈ Icc (-tau) 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0),
      EqOn (((P k).metric s).pullbackCoefficients psi)
        (fun x => generalizedPullbackCoefficients G (k + N) q (s, x)) U := by
    intro k s hs hsG x hx
    have hstage_x : c.symm x ∈ G.exhaustion.space (k + N) := by
      have hy : (psi x).val ∈ (Y : Set G.limit.carrier.carrier) := (psi x).property
      rw [hpsival x hx] at hy
      exact hstage k hy
    let X : GeneralizedSliceCarrier :=
      (S.flow (G.subsequence (k + N))).slice
        ((S.base (G.subsequence (k + N))).1 + s /
          S.scale (G.subsequence (k + N)))
    let : TopologicalSpace X.carrier := X.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X.carrier := X.chartedSpace
    let : IsManifold (𝓡 3) ∞ X.carrier := X.isManifold
    let ef : G.limit.carrier.carrier → X.carrier :=
      (G.embedding (k + N)).forward s hsG
    have hlocal : (fun y : E => ef (c.symm y)) =ᶠ[𝓝 x]
        (fun y : E => ef ((psi y).val)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hpsival y hy]
    have hsub : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (Subtype.val : Y → G.limit.carrier.carrier) (psi x) :=
      contMDiff_subtype_val.contMDiffAt
    have hpoint : ef (c.symm x) = ef ((psi x).val) := by
      rw [hpsival x hx]
    have hderiv (v : E) :
        mfderiv (𝓡 3) (𝓡 3)
            (ef ∘ c.symm) x v =
          mfderiv (𝓡 3) (𝓡 3)
            (ef ∘
              (Subtype.val : Y → G.limit.carrier.carrier) ∘ psi) x v := by
      have hd := hlocal.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
      convert congrArg (fun f => f v) hd using 1 <;> rfl
    have hef_c : ContMDiffAt (𝓡 3) (𝓡 3) ∞ ef (c.symm x) := by
      simpa only [ef] using
        ((G.embedding (k + N)).forward_smooth s hsG (c.symm x) hstage_x).contMDiffAt
          ((G.exhaustion.space_open (k + N)).mem_nhds hstage_x)
    have hef_psi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ ef ((psi x).val) := by
      have hstage_psi : (psi x).val ∈ G.exhaustion.space (k + N) :=
        hstage k (psi x).property
      simpa only [ef] using
        ((G.embedding (k + N)).forward_smooth s hsG (psi x).val
          hstage_psi).contMDiffAt
          ((G.exhaustion.space_open (k + N)).mem_nhds
            hstage_psi)
    have hvalpsi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        ((Subtype.val : Y → G.limit.carrier.carrier) ∘ psi) x :=
      hsub.comp x (hpsi_at hx)
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x := by
      dsimp [c]
      exact contMDiffOn_extChartAt_symm (n := ∞) q |>.contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hUc hx))
    have hcomp_c (v : E) := mfderiv_comp_apply x
      (hef_c.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) v
    have hcomp_psi (v : E) := mfderiv_comp_apply x
      (hef_psi.mdifferentiableAt (by simp))
      (hvalpsi.mdifferentiableAt (by simp)) v
    have hcomp_psi' (v : E) :
        mfderiv (𝓡 3) (𝓡 3)
            (ef ∘ (Subtype.val : Y → G.limit.carrier.carrier) ∘ psi) x v =
          mfderiv (𝓡 3) (𝓡 3) ef ((psi x).val)
            (mfderiv (𝓡 3) (𝓡 3)
              ((Subtype.val : Y → G.limit.carrier.carrier) ∘ psi) x v) := by
      simpa only [Function.comp_apply] using hcomp_psi v
    ext v w
    simp only [generalizedPullbackCoefficients, dif_pos hsG]
    unfold RiemannianMetric.pullbackCoefficients
    change ((P k).metric s).inner (psi x)
      (mfderiv (𝓡 3) (𝓡 3) psi x v)
      (mfderiv (𝓡 3) (𝓡 3) psi x w) = _
    rw [hmetric k s hs hsG (psi x)
      (mfderiv (𝓡 3) (𝓡 3) psi x v)
      (mfderiv (𝓡 3) (𝓡 3) psi x w)]
    dsimp only [GeneralizedFlowCylinder.pullbackInner]
    have hsubpsi := mfderiv_comp_apply x
      (hsub.mdifferentiableAt (by simp))
      ((hpsi_at hx).mdifferentiableAt (by simp))
    rw [← hsubpsi v, ← hsubpsi w, ← hcomp_psi' v, ← hcomp_psi' w,
      ← hderiv v, ← hderiv w, hcomp_c v, hcomp_c w, hpoint]
    change _ = (normalizedBlowupSliceMetric S (G.subsequence (k + N)) s).inner
      (ef (c.symm x))
      (mfderiv (𝓡 3) (𝓡 3) (ef ∘ c.symm) x v)
      (mfderiv (𝓡 3) (𝓡 3) (ef ∘ c.symm) x w)
    rw [hcomp_c v, hcomp_c w]
    simp only [normalizedBlowupSliceMetric, M13.scaleSmoothMetric_inner]
    rw [hpoint]
  have hfirst :
      (∀ k s (hs : s ∈ Icc (-tau) 0)
        (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0),
      EqOn (((P k).metric s).pullbackCoefficients psi)
        (fun x => generalizedPullbackCoefficients G (k + N) q (s, x)) U) := hcoeff_eq
  have hconverges : ∀ r : ℕ, ∀ K : Set (ℝ × E),
      IsCompact K → K ⊆ Ioc (-T) 0 ×ˢ U →
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ r
          (((P k).metric z.1).pullbackCoefficients psi) z.2)
        (fun z => iteratedFDeriv ℝ r
          (fun y => (G.limit.flow.metric z.1).pullbackCoefficients c.symm y) z.2) atTop K := by
    intro r K hK hKU
    have hvalid : ∀ᶠ k : ℕ in atTop, K ⊆
        Icc (-G.exhaustion.time (k + N)) 0 ×ˢ c.target := by
      obtain ⟨L, hL⟩ := eventually_atTop.mp
        (G.exhaustion.time_cofinal (Prod.fst '' K) (hK.image continuous_fst)
          (by rintro _ ⟨z, hz, rfl⟩; exact (hKU hz).1))
      filter_upwards [eventually_ge_atTop L] with k hk
      intro z hz
      exact ⟨hL (k + N) (by omega) (mem_image_of_mem _ hz), hUc (hKU hz).2⟩
    have hKc : K ⊆ blowupMetricChartDomain G.limit q := by
      intro z hz
      exact ⟨(hKU hz).1, hUc (hKU hz).2⟩
    have hjet := tendstoUniformlyOn_generalized_bilinear_spatial_jets
      G q r hK hKc
    have hshift : TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ r
          (fun y : E => generalizedPullbackCoefficients G (k + N) q (z.1, y)) z.2)
        (fun z : ℝ × E => iteratedFDeriv ℝ r
          (fun y : E => (G.limit.flow.metric z.1).pullbackCoefficients c.symm y) z.2)
        atTop K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact (tendsto_add_atTop_nat N).eventually
        ((Metric.tendstoUniformlyOn_iff.mp hjet) ε hε)
    apply hshift.congr
    filter_upwards [hvalid] with k hk
    intro z hz
    have hs : z.1 ∈ Icc (-tau) 0 :=
      ⟨by linarith [(hKU hz).1.1], (hKU hz).1.2⟩
    have heq :
        (fun y : E => ((P k).metric z.1).pullbackCoefficients psi y) =ᶠ[𝓝 z.2]
          (fun y : E => generalizedPullbackCoefficients G (k + N) q (z.1, y)) := by
      filter_upwards [hU.mem_nhds (hKU hz).2] with y hy
      exact hcoeff_eq k z.1 hs (hk hz).1 hy
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm
  have hbounds : ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ alpha beta : ℝ, 0 < alpha ∧ 0 ≤ beta ∧
        (∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K, ∀ v,
          alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients psi x v v ∧
            ((P k).metric t).pullbackCoefficients psi x v v ≤ beta * ‖v‖ ^ 2) ∧
        ∀ m : ℕ, ∃ Bm : ℝ, 0 ≤ Bm ∧ ∀ᶠ k : ℕ in atTop,
          ∀ z ∈ Icc (-tau) 0 ×ˢ K,
            ‖iteratedFDerivWithin ℝ m
              (fun z => ((P k).metric z.1).pullbackCoefficients psi z.2)
              (Icc (-tau) 0 ×ˢ U) z‖ ≤ Bm := by
    intro K hK hKU
    let B0 := (G.limit.flow.metric 0).pullbackCoefficients c.symm
    have hBcont : ContinuousOn B0 K := by
      intro x hx
      exact ((G.limit.flow.metric 0).contDiffAt_pullbackCoefficients
        ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds
            (hUc (hKU hx))))).continuousAt.continuousWithinAt
    have hBdiff {x : E} (hx : x ∈ K) : ContDiffAt ℝ ∞ B0 x :=
      (G.limit.flow.metric 0).contDiffAt_pullbackCoefficients
        ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hUc (hKU hx))))
    have hBpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B0 x v v := by
      intro x hx v hv
      apply (G.limit.flow.metric 0).pos
      have hi0 : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm (hUc (hKU hx))
      intro hz
      apply hv
      apply hi0.injective
      rw [map_zero]
      exact hz
    obtain ⟨a, ha, hAlower⟩ := exists_uniform_bilinear_family_lower_bound hK hBcont hBpos
    have hconvK : ∀ m : ℕ, TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ m
          (((P k).metric 0).pullbackCoefficients psi) x)
        (iteratedFDeriv ℝ m B0) atTop K := by
      intro m
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain hε' := Metric.tendstoUniformlyOn_iff.mp
        (hconverges m ({0} ×ˢ K) (isCompact_singleton.prod hK) (by
          rintro ⟨t, x⟩ ⟨ht, hx⟩
          have ht0 : t = 0 := mem_singleton_iff.mp ht
          subst t
          exact ⟨⟨neg_lt_zero.mpr hT, le_rfl⟩, hKU hx⟩)) ε hε
      filter_upwards [hε'] with k hk
      intro x hx
      simpa only [B0] using hk (0, x) ⟨mem_singleton _, hx⟩
    have hconv0 := hconvK 0
    have hcoeff : TendstoUniformlyOn
        (fun k => ((P k).metric 0).pullbackCoefficients psi) B0 atTop K := by
      have h := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn hconv0
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using! h
    obtain ⟨b, hb, hBbound⟩ := hcoeff.exists_eventual_norm_bound hK hBcont
    have hterm : ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v,
        (a / 2) * ‖v‖ ^ 2 ≤ ((P k).metric 0).pullbackCoefficients psi x v v ∧
          ((P k).metric 0).pullbackCoefficients psi x v v ≤ b * ‖v‖ ^ 2 := by
      filter_upwards [hBbound,
        Metric.tendstoUniformlyOn_iff.mp hcoeff (a / 2) (by positivity)] with k hk hc0
      intro x hx v
      have hdist := hc0 x hx
      have hnorm : ‖((P k).metric 0).pullbackCoefficients psi x - B0 x‖ ≤ a / 2 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hdist.le
      have herr : |((P k).metric 0).pullbackCoefficients psi x v v - B0 x v v| ≤
          (a / 2) * ‖v‖ ^ 2 := by
        calc
          |((P k).metric 0).pullbackCoefficients psi x v v - B0 x v v| ≤
              ‖((P k).metric 0).pullbackCoefficients psi x - B0 x‖ *
                (‖v‖ * ‖v‖) := by
            simpa only [sub_apply, Real.norm_eq_abs, mul_assoc] using
              (((P k).metric 0).pullbackCoefficients psi x - B0 x).le_opNorm₂ v v
          _ ≤ (a / 2) * (‖v‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_right hnorm
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (a / 2) * ‖v‖ ^ 2 := by rw [pow_two]
      constructor
      · nlinarith [hAlower x hx v, (abs_le.mp herr).1]
      · have hnorm' := ContinuousLinearMap.le_opNorm₂
          (((P k).metric 0).pullbackCoefficients psi x) v v
        calc
          ((P k).metric 0).pullbackCoefficients psi x v v ≤
              |((P k).metric 0).pullbackCoefficients psi x v v| := le_abs_self _
          _ ≤ ‖((P k).metric 0).pullbackCoefficients psi x‖ * (‖v‖ * ‖v‖) := by
            simpa only [Real.norm_eq_abs, mul_assoc] using hnorm'
          _ ≤ b * ‖v‖ ^ 2 := by
            simpa only [pow_two] using mul_le_mul_of_nonneg_right (hk x hx)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    obtain ⟨D, hD, hDcurv⟩ := hcurv 0
    let alpha := Real.exp (-2 * (3 : ℝ) * D * tau) * (a / 2)
    let beta := Real.exp (2 * (3 : ℝ) * D * tau) * b
    have halpha : 0 < alpha := by dsimp [alpha]; positivity
    have hbeta : 0 ≤ beta := mul_nonneg (Real.exp_pos _).le (by linarith)
    have hell : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K, ∀ v,
        alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients psi x v v ∧
          ((P k).metric t).pullbackCoefficients psi x v v ≤ beta * ‖v‖ ^ 2 := by
      filter_upwards [hterm] with k hk t ht x hx v
      exact M28.backward_pullback_ellipticity (P k) htau hD psi x
        (fun s hs => by
          simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using
            hDcurv k s hs (psi x)) (hk x hx) ht v
    refine ⟨alpha, beta, halpha, hbeta, hell, ?_⟩
    apply M28.eventually_within_bounds_closed_backward_of_curvature atTop htau P
      (fun _ => U) (fun _ => K) (fun _ => psi)
      (fun _ => hU) (fun _ => hKU) (fun _ => hpsi) (fun _ => hi)
      halpha hbeta hell
    · intro s
      obtain ⟨D, hD, hbound⟩ := hcurv s
      exact ⟨D, hD, Eventually.of_forall (fun k t ht x hx =>
        hbound k t (Ioo_subset_Icc_self ht) (psi x))⟩
    · intro j
      have hcont : ContinuousOn (iteratedFDeriv ℝ j B0) K := fun x hx =>
        ((hBdiff hx).continuousAt_iteratedFDeriv
          (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)).continuousWithinAt
      obtain ⟨Z, hZ, hbound⟩ := (hconvK j).exists_eventual_norm_bound hK hcont
      exact ⟨Z, by linarith, hbound⟩
  exact ⟨hfirst, hconverges, hbounds⟩

end PoincareConjecture.M30
