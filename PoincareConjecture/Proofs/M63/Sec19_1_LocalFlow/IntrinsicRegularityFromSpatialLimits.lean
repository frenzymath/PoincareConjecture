import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1EmbeddingPushforward
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2NormalizationContinuity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelC2Transport
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedNormalSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialArclengthGauge
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackRicciRegularity
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SmoothRelabeling
import PoincareConjecture.Proofs.M63.Mathlib.NormalizedSpatialPathBootstrap
import PoincareConjecture.Proofs.M63.Adapters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem intrinsic_regularity_of_spatial_jets_and_speed_primitive
    [T2Space M] (F : RicciFlow n M (Icc a b)) {T : ℝ} (_haT : a < T)
    {c : ℝ → ℝ → M} (hc : M63C2ShrinkingCurveOn F c (Icc a T))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (hspatial : ∀ i t, a < t → t ≤ T →
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M)))
    (hclosed : ∀ tau s, a < tau → tau ≤ s → s ≤ T → ∀ i,
      ContinuousOn (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Icc tau s))
    (hspeed : ∀ tau t, a < tau → tau ≤ t → t ≤ T → ∀ x,
      curveSpeed F c t x = curveSpeed F c tau x * Real.exp
        (-∫ u in tau..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x)) :
    M63IntrinsicRegularityOn F c (Icc a T) := by
  have hnormalized (tau s : ℝ) (hat : a < tau) (hts : tau < s) (hsT : s ≤ T) :
      ∃ (phi : ℝ ≃ₜ ℝ) (d : ℝ → ℝ → M), ContDiff ℝ 2 (phi : ℝ → ℝ) ∧
        (∀ x, 0 < deriv phi x) ∧ (∀ x t, d (phi x) t = c x t) ∧
        M63SmoothShrinkingCurveOn F d (Icc tau s) := by
    have hslab : Icc tau s ⊆ Icc a T :=
      fun _ ht => ⟨hat.le.trans ht.1, ht.2.trans hsT⟩
    have htau : tau ∈ Icc a T := hslab ⟨le_rfl, hts.le⟩
    obtain ⟨_hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
      _hshift, hpsishift, _hperiod, _hregular, _himm, hanchor, _hprincipal⟩ :=
      exists_c2_constant_speed_relabeling F (fun x => c x tau) tau
        (hc.periodic tau htau) (hc.spatial_regular tau htau) (hc.immersed tau htau)
    let psi : ℝ → ℝ := phi.symm
    let d := fun x t => c (psi x) t
    let q := fun x t => e (d x t)
    let v := fun x t => curveSpeed F d t x
    let K := fun (i : ℕ) (t x : ℝ) => match i with
      | 0 => spatialUnitTangent F c t x
      | i + 1 => m63CurvatureJet F c i t x
    let R : ℕ → ℝ → ℝ → W :=
      fun i x t => mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t) (K i t (psi x))
    let A : (ℝ × W) × (W × W) → ℝ := fun z =>
      (F.connection z.1.1).ricci (ρ z.1.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1) +
        (F.metric z.1.1).inner (ρ z.1.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
    let B : (ℝ × W) × (W × W) → W := fun z =>
      coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
    let L : ℝ × ℝ → ℝ × ℝ := fun z => (psi z.1, z.2)
    have hL : Continuous L := (hpsi.continuous.comp continuous_fst).prodMk continuous_snd
    have hLJ : MapsTo L (univ ×ˢ Icc tau s) (univ ×ˢ Icc a T) :=
      fun _ hz => ⟨mem_univ _, hslab hz.2⟩
    have hLS : MapsTo L (univ ×ˢ Icc tau s) (univ ×ˢ Icc tau s) :=
      fun _ hz => ⟨mem_univ _, hz.2⟩
    have hdata := c2ShrinkingCurve_embedded_closed_data hc he
    have hq : ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (univ ×ˢ Icc tau s) :=
      hdata.2.2.1.comp hL.continuousOn hLJ
    have hvold : ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 (psi z.1))
        (univ ×ˢ Icc tau s) :=
      (c2ShrinkingCurve_speed_normalization_continuousOn F hc).1.comp hL.continuousOn hLJ
    have hvpos (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) : 0 < curveSpeed F c t x :=
      Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t (hslab ht) x))
    have hpsid (x : ℝ) : HasDerivAt psi (deriv psi x) x :=
      (hpsi.differentiable (by norm_num) x).hasDerivAt
    have hvspec (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        v x t = deriv psi x * curveSpeed F c t (psi x) :=
      curveSpeed_comp F c ((hc.spatial_regular t (hslab ht)).mdifferentiable
        (by norm_num) (psi x)) (hpsid x) (hpsipos x).le
    have hpush : Continuous (fun p : TangentBundle (𝓡 n) M =>
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
      (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).continuous.comp
        (he.continuous_tangentMap (by simp))
    have hR : ∀ i, ContinuousOn (fun z : ℝ × ℝ => R i z.1 z.2)
        (univ ×ˢ Icc tau s) := by
      intro i
      cases i with
      | zero =>
        have hfirst := hdata.2.2.2.1.comp hL.continuousOn hLJ
        have hnorm := (hvold.inv₀ (fun z hz => (hvpos z.2 hz.2 (psi z.1)).ne')).smul hfirst
        apply hnorm.congr
        intro z hz
        change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (psi z.1) z.2)
            ((curveSpeed F c z.2 (psi z.1))⁻¹ •
              curveVelocity (n := n) (fun y => c y z.2) (psi z.1)) =
          (curveSpeed F c z.2 (psi z.1))⁻¹ • deriv (fun y => e (c y z.2)) (psi z.1)
        rw [map_smul, (hdata.2.1 z.2 (hslab hz.2) (psi z.1)).deriv]
      | succ i =>
        exact (hpush.comp_continuousOn (hclosed tau s hat hts.le hsT i)).comp
          hL.continuousOn hLS
    have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
    have hBval (i : ℕ) (t x : ℝ) : B ((t, q x t), (R 0 x t, R i x t)) =
        coordinateHessian (F.connection t) e (d x t) (K 0 t (psi x)) (K i t (psi x)) := by
      dsimp only [B, q, R]
      erw [hleft (d x t) (K 0 t (psi x)), hleft (d x t) (K i t (psi x)), hρe (d x t)]
    have hvelocity (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        curveVelocity (n := n) (fun y => c y t) x = curveSpeed F c t x • K 0 t x := by
      symm
      change curveSpeed F c t x • ((curveSpeed F c t x)⁻¹ •
        curveVelocity (n := n) (fun y => c y t) x) = _
      rw [smul_smul, mul_inv_cancel₀ (hvpos t ht x).ne', one_smul]
    have hqder (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        HasDerivAt (fun y => q y t) (v x t • R 0 x t) x := by
      have hd := (hdata.2.1 t (hslab ht) (psi x)).scomp x (hpsid x)
      apply hd.congr_deriv
      change deriv psi x • (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (psi x) t)
        (curveVelocity (n := n) (fun y => c y t) (psi x))) = v x t • R 0 x t
      rw [hvelocity t ht (psi x), map_smul, smul_smul, ← hvspec t ht x]
    have hKnext (i : ℕ) (t x : ℝ) : K (i + 1) t x =
        (curveSpeed F c t x)⁻¹ • rampHorizontalCovariantDerivative (F.connection t)
          (fun y => c y t) (K i t) x := by
      cases i <;> rfl
    have hcovold (i : ℕ) (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        rampHorizontalCovariantDerivative (F.connection t) (fun y => c y t) (K i t) x =
          curveSpeed F c t x • K (i + 1) t x := by
      rw [hKnext, smul_smul, mul_inv_cancel₀ (hvpos t ht x).ne', one_smul]
    have hKi (i : ℕ) (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
          (fun y => (⟨c y t, K i t y⟩ : TangentBundle (𝓡 n) M)) x := by
      cases i with
      | zero =>
        exact unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t (hslab ht))
          (hc.immersed t (hslab ht)) x
      | succ i => exact hspatial i t (hat.trans_le ht.1) (ht.2.trans hsT) x
    have hscale (t : ℝ) (p : M) (X Y : TangentSpace (𝓡 n) p) (r : ℝ) :
        coordinateHessian (F.connection t) e p (r • X) Y =
          r • coordinateHessian (F.connection t) e p X Y := by
      ext i
      have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q i) :=
        (EuclideanSpace.proj i).contDiff.contMDiff.comp he
      obtain ⟨D, hD⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hei).1 p
      have hrep (v w : TangentSpace (𝓡 n) p) :
          (F.connection t).hessian (fun q => e q i) p v w = D ![v, w] := hD ![v, w]
      change (F.connection t).hessian (fun q => e q i) p (r • X) Y =
        r * (F.connection t).hessian (fun q => e q i) p X Y
      rw [hrep, hrep]
      simpa only [Matrix.vecCons, smul_eq_mul] using D.cons_smul ![Y] r X
    have hRder (i : ℕ) (t : ℝ) (ht : t ∈ Icc tau s) (x : ℝ) :
        HasDerivAt (fun y => R i y t)
          (v x t • (B ((t, q x t), (R 0 x t, R i x t)) + R (i + 1) x t)) x := by
      have hpsione : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 psi x :=
        (hpsi.of_le (by norm_num)).contMDiff.contMDiffAt
      have hd : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun y => d y t) x :=
        (((hc.spatial_regular t (hslab ht)).comp hpsi.contMDiff).of_le (by norm_num)) x
      have hY : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
          (fun y => (⟨d y t, K i t (psi y)⟩ : TangentBundle (𝓡 n) M)) x :=
        (hKi i t ht (psi x)).comp x hpsione
      have hvel : curveVelocity (n := n) (fun y => d y t) x = v x t • K 0 t (psi x) := by
        rw [curveVelocity_comp
          ((hc.spatial_regular t (hslab ht)).mdifferentiable (by norm_num) (psi x))
          (hpsid x), hvelocity t ht (psi x), smul_smul, ← hvspec t ht x]
      have hcov : rampHorizontalCovariantDerivative (F.connection t)
          (fun y => d y t) (fun y => K i t (psi y)) x = v x t • K (i + 1) t (psi x) := by
        rw [pullback_comp (F.connection t)
          ((hKi i t ht (psi x)).mdifferentiableAt (by norm_num)) (hpsid x),
          hcovold i t ht (psi x), smul_smul, ← hvspec t ht x]
      have hp := hasDerivAt_embedding_pushforward_of_contMDiffAt_one
        (F.connection t) he hd (fun y => K i t (psi y)) hY
      apply hp.congr_deriv
      change HAdd.hAdd (α := W) (β := W) (γ := W)
        (coordinateHessian (F.connection t) e (d x t)
          (curveVelocity (n := n) (fun y => d y t) x) (K i t (psi x)))
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t)
          (rampHorizontalCovariantDerivative (F.connection t)
            (fun y => d y t) (fun y => K i t (psi y)) x)) =
        v x t • (B ((t, q x t), (R 0 x t, R i x t)) + R (i + 1) x t)
      rw [hvel, hcov, hscale, map_smul, smul_add, hBval]
    have htime : Icc tau s ⊆ Icc a b := hslab.trans hc.domain_subset
    have hric := flow_pullback_ricci_contDiffOn F hU hρ
    have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
      (contMDiff_const (c := (0 : ℝ)))).1
    have hfirstMap : ContDiff ℝ ∞
        (fun z : (ℝ × W) × (W × W) => (z.1, z.2.1)) := by fun_prop
    have hsecondMap : ContDiff ℝ ∞
        (fun z : (ℝ × W) × (W × W) => (z.1, z.2.2)) := by fun_prop
    have hAfst := hric.comp (s := (Icc tau s ×ˢ U) ×ˢ univ)
      hfirstMap.contDiffOn (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, mem_univ _⟩)
    have hAsnd := hmetric.comp (s := (Icc tau s ×ˢ U) ×ˢ univ)
      hsecondMap.contDiffOn (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, mem_univ _⟩)
    have hA : ContDiffOn ℝ ∞ A ((Icc tau s ×ˢ U) ×ˢ univ) := hAfst.add hAsnd
    have hB : ContDiffOn ℝ ∞ B ((Icc tau s ×ˢ U) ×ˢ univ) :=
      (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).mono
        (fun z hz => ⟨⟨htime hz.1.1, hz.1.2⟩, hz.2⟩)
    have hAvalue (t x : ℝ) : A ((t, q x t), (R 0 x t, R 1 x t)) =
        m62TangentRicci F c t (psi x) + m62CurvatureSquared F c t (psi x) := by
      dsimp only [A, q, R]
      erw [hleft (d x t) (K 0 t (psi x)), hleft (d x t) (K 1 t (psi x)), hρe (d x t)]
      rfl
    let v0 := (∫ x in (0 : ℝ)..curvePeriod, curveSpeed F c tau x) / curvePeriod
    change ∀ x, v x tau = v0 at hanchor
    have hvformula (x : ℝ) (t : ℝ) (ht : t ∈ Icc tau s) :
        v x t = v0 * Real.exp (-∫ u in tau..t, A ((u, q x u), (R 0 x u, R 1 x u))) := by
      have hInt : (∫ u in tau..t, A ((u, q x u), (R 0 x u, R 1 x u))) =
          ∫ u in tau..t, m62TangentRicci F c u (psi x) +
            m62CurvatureSquared F c u (psi x) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        exact hAvalue u x
      rw [hInt, ← hanchor x, hvspec t ht x, hvspec tau ⟨le_rfl, hts.le⟩ x,
        hspeed tau t hat ht.1 (ht.2.trans hsT) (psi x)]
      ring
    obtain ⟨Q, _V, _Rpath, hQvalue, _hVvalue, _hRvalue, hQ, _hV, _hRp⟩ :=
      exists_contDiff_pathFamily_of_normalized_spatial_recurrences hts hU A B hA hB
        q v R v0 hq hR (fun x t _ => heU (mem_range_self (d x t))) hvformula hqder hRder
    have hslice (t : Icc tau s) : ContDiff ℝ ∞ (fun x => q x t) := by
      let ev : C(Icc tau s, W) →L[ℝ] W := ContinuousMap.evalCLM ℝ t
      have heval := ev.contDiff.comp hQ
      change ContDiff ℝ ∞ (fun x => Q x t) at heval
      have heq : (fun x => Q x t) = fun x => q x t := funext fun x => hQvalue x t
      rwa [heq] at heval
    have hjet (k : ℕ) (t : Icc tau s) :
        iteratedDeriv k (fun x => q x t) = fun x => iteratedDeriv k Q x t := by
      induction k with
      | zero =>
        simp only [iteratedDeriv_zero]
        exact funext (fun x => (hQvalue x t).symm)
      | succ k ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
        funext x
        have hqd := (hQ.differentiable_iteratedDeriv k
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
        exact ((ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp_hasDerivAt x hqd).deriv
    have hjets (k : ℕ) : ContinuousOn
        (fun z : ℝ × ℝ => iteratedDeriv k (fun x => q x z.2) z.1)
        (univ ×ˢ Icc tau s) := by
      have hpaths : Continuous (fun z : ℝ × ℝ => iteratedDeriv k Q z.1) :=
        (hQ.continuous_iteratedDeriv k
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp continuous_fst
      have hclamp : Continuous (fun z : ℝ × ℝ => projIcc tau s hts.le z.2) :=
        continuous_projIcc.comp continuous_snd
      have hcont := continuous_eval.comp (hpaths.prodMk hclamp)
      apply hcont.continuousOn.congr
      intro z hz
      change iteratedDeriv k (fun x => q x z.2) z.1 =
        iteratedDeriv k Q z.1 (projIcc tau s hts.le z.2)
      rw [projIcc_of_mem _ hz.2]
      exact congrFun (hjet k ⟨z.2, hz.2⟩) z.1
    have hd : M63C2ShrinkingCurveOn F d (Icc tau s) :=
      c2_restrict (c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpsipos hpsishift) hslab
    have hsmooth : M63SmoothShrinkingCurveOn F d (Icc tau s) :=
      c2ShrinkingCurve_smooth_of_embedded_spatial_jets F hts hd he hU heU hρ hρe
        (fun t ht => hslice ⟨t, Ioo_subset_Icc_self ht⟩)
        (fun k => (hjets k).mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
    refine ⟨phi, d, hphi, hpos, ?_, hsmooth⟩
    intro x t
    change c (phi.symm (phi x)) t = c x t
    rw [phi.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · intro i
    rw [interior_Icc]
    apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    obtain ⟨tau, hat, htt⟩ := exists_between hz.2.1
    obtain ⟨s, hts', hsT⟩ := exists_between hz.2.2
    have hts : tau < s := htt.trans hts'
    obtain ⟨phi, d, hphi, hpos, heq, hd⟩ := hnormalized tau s hat hts hsT.le
    have hcEq : (fun x t => d (phi x) t) = c := funext fun x => funext (heq x)
    let F' := m63RestrictClosedFlow F tau s hd.1.domain_subset hts
    have hd' : M62ShrinkingCurve F' d := m63SmoothRestriction hd tau s Subset.rfl hts
    have hrestrict (q : ℝ → ℝ → M) (j : ℕ) (t x : ℝ) :
        m63CurvatureJet F' q j t x = m63CurvatureJet F q j t x := by
      induction j generalizing x with
      | zero => rfl
      | succ j ih =>
        change (curveSpeed F' q t x)⁻¹ • rampHorizontalCovariantDerivative
            (F'.connection t) (fun y => q y t) (fun y => m63CurvatureJet F' q j t y) x =
          (curveSpeed F q t x)⁻¹ • rampHorizontalCovariantDerivative
            (F.connection t) (fun y => q y t) (fun y => m63CurvatureJet F q j t y) x
        rw [show (fun y => m63CurvatureJet F' q j t y) =
          (fun y => m63CurvatureJet F q j t y) from funext ih]
        rfl
    have hmap : ContDiff ℝ 1 (fun y : ℝ × ℝ => (phi y.1, y.2)) :=
      ((hphi.of_le (by norm_num)).comp contDiff_fst).prodMk contDiff_snd
    have hji := ((curvatureJet_joint_contMDiff F' d hd' i).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).comp (s := univ ×ˢ Ioo tau s)
      hmap.contMDiff.contMDiffOn (fun _ hy => ⟨mem_univ _, hy.2⟩)
    have hactual : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun y : ℝ × ℝ =>
          (⟨c y.1 y.2, m63CurvatureJet F c i y.2 y.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Ioo tau s) := by
      apply hji.congr
      intro y hy
      apply Bundle.TotalSpace.ext (heq y.1 y.2).symm
      apply heq_of_eq
      have htrans := smooth_curvatureJet_comp F' d hd'
        (hphi.differentiable (by norm_num)) hpos hy.2 i y.1
      rw [hcEq, hrestrict c i y.2 y.1] at htrans
      exact htrans
    refine ⟨univ ×ˢ Ioo tau s, isOpen_univ.prod isOpen_Ioo,
      ⟨mem_univ _, htt, hts'⟩, ?_⟩
    exact hactual.mono inter_subset_right
  · intro tau s hat hts hslab i
    have hsT : s ≤ T := (hslab ⟨hts, le_rfl⟩).2
    exact hclosed tau s hat hts hsT i

end PoincareConjecture.M63
