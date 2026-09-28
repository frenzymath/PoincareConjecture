import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedCurvatureJetIdentification
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedCurvatureJetSpatial
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TracePeriodicCurvature
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicDerivativeFilterLimit
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M63

variable {n : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : Real}

local notation "W" => EuclideanSpace Real ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, Real)

theorem exists_terminal_embeddedCurvatureJets
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {alpha tau S : Real} (haa : a ≤ alpha) (hat : alpha < tau)
    (htS : tau < S) (hSb : S ≤ b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(Real, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(Real, W) (𝓡 n) ∞ ρ U)
    (hρe : ∀ p, ρ (e p) = p)
    {c : Real → Real → M}
    (hc : M63SmoothShrinkingCurveOn F c (Icc alpha S))
    (hjets : ∀ i : Nat, ∃ K : Real, 0 ≤ K ∧
      ∀ t ∈ Ioo tau S, ∀ x : Real,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ K)
    (hgradient : ∃ G : Real, 0 ≤ G ∧
      ∀ t ∈ Ioo tau S, ∀ x : Real, |deriv (curveSpeed F c t) x| ≤ G) :
    ∃ η : Nat → C(Icc tau S, X),
      (∀ i (t : Icc tau S) (x : Real),
        η i t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(Real, W) e (c x t) (m63CurvatureJet F c i t x)) ∧
      (∀ i (t : Icc tau S) (x : Real),
        HasDerivAt (fun y : Real => η i t (y : AddCircle curvePeriod))
          (curveSpeed F c t x •
            (HAdd.hAdd (α := W) (β := W) (γ := W)
              (η (i + 1) t (x : AddCircle curvePeriod))
              (coordinateHessian (F.connection t) e (c x t)
                (spatialUnitTangent F c t x) (m63CurvatureJet F c i t x)))) x) ∧
      (∀ i (t : Icc tau S),
        ContMDiff 𝓘(Real, Real) ((𝓡 n).prod (𝓡 n)) 1
          (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M))) ∧
      ∀ i, ContinuousOn
        (fun z : Real × Real =>
          (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Icc tau S) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  have haS : alpha < S := hat.trans htS
  have hsubF : Icc alpha S ⊆ Icc a b := Icc_subset_Icc haa hSb
  let F0 := m63RestrictClosedFlow F alpha S hsubF haS
  have hc0 : M62ShrinkingCurve F0 c :=
    m63SmoothRestriction hc alpha S Subset.rfl haS
  have hjet0 (i : Nat) (t x : Real) :
      m63CurvatureJet F0 c i t x = m63CurvatureJet F c i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F c t (fun y => m63CurvatureJet F0 c i t y) x =
        m62SpatialDerivative F c t (fun y => m63CurvatureJet F c i t y) x
      rw [show (fun y => m63CurvatureJet F0 c i t y) =
        (fun y => m63CurvatureJet F c i t y) from funext ih]
  let C := Icc tau S
  let Path := C(C, X)
  let endTime : C := ⟨S, htS.le, le_rfl⟩
  let pi : Real → C := projIcc tau S htS.le
  have hpi (t : Real) (ht : t ∈ C) : pi t = ⟨t, ht⟩ := projIcc_of_mem htS.le ht
  have hC : C ⊆ Icc alpha S := Icc_subset_Icc_left hat.le
  have htime (t : Real) (ht : t ∈ Ico tau S) : t ∈ Ioo alpha S :=
    ⟨hat.trans_le ht.1, ht.2⟩
  let A : Nat → Real × Real → W := fun i z =>
    mfderiv (𝓡 n) 𝓘(Real, W) e (c z.1 z.2) (m63CurvatureJet F0 c i z.2 z.1)
  let Ω : Set (Real × Real) := univ ×ˢ Ioo alpha S
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hpush : ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(Real, W) ∞
      (fun p : TangentBundle (𝓡 n) M => (mfderiv (𝓡 n) 𝓘(Real, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(Real, W)).comp
      (he.contMDiff_tangentMap (by simp))
  have hA (i : Nat) : ContDiffOn Real ∞ (A i) Ω :=
    (hpush.comp_contMDiffOn (curvatureJet_joint_contMDiff F0 c hc0 i)).contDiffOn
  have hdx (i : Nat) (t : Real) (ht : t ∈ Ico tau S) (x : Real) :
      HasDerivAt (fun y => A i (y, t)) (M08.coordinatePartialS (A i) (x, t)) x :=
    M08.coordinateSlice_fst_hasDerivAt (A i) (p := (x, t))
      (((hA i).contDiffAt (hΩ.mem_nhds ⟨mem_univ _, htime t ht⟩)).differentiableAt
        (by simp))
  have descend (J : Set Real) (f : Real × Real → W)
      (hf : ContinuousOn f (univ ×ˢ J))
      (hp : ∀ t ∈ J, Function.Periodic (fun x => f (x, t)) curvePeriod) :
      ∃ g : Real → X, ContinuousOn g J ∧
        ∀ t ∈ J, ∀ x : Real, g t (x : AddCircle curvePeriod) = f (x, t) := by
    let g : Real → X := fun t => if ht : t ∈ J then
      ⟨(hp t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
          (hf.comp_continuous (continuous_id.prodMk continuous_const)
            (fun _ => ⟨mem_univ _, ht⟩))⟩ else 0
    have hg (t : Real) (ht : t ∈ J) (x : Real) :
        g t (x : AddCircle curvePeriod) = f (x, t) := by
      simp only [g, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    refine ⟨g, continuousOn_iff_continuous_domRestrict.mpr ?_, hg⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : J × Real => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    exact (hf.comp_continuous
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨mem_univ _, p.1.2⟩)).congr (fun p => (hg p.1 p.1.2 p.2).symm)
  have hderivper {f : Real → W} (hp : Function.Periodic f curvePeriod) :
      Function.Periodic (deriv f) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun g : Real → W => deriv g x) (funext hp)
  have hdata := c2ShrinkingCurve_embedded_closed_data (m63C2_of_m62 hc0) he
  have hrper (t : Real) (ht : t ∈ Icc alpha S) :
      Function.Periodic (fun x => e (c x t)) curvePeriod :=
    fun x => congrArg e (hc0.periodic t ht x)
  obtain ⟨r0, hr0, hrrep⟩ := descend C (fun z => e (c z.1 z.2))
    (hdata.2.2.1.mono (prod_mono Subset.rfl hC)) (fun t ht => hrper t (hC ht))
  let r : Path := ⟨fun t => r0 t, hr0.domRestrict⟩
  have hspeedC := M62.speed_continuousOn F0 c hc0
  have hvpos (t : Real) (ht : t ∈ Icc alpha S) (x : Real) :
      0 < curveSpeed F0 c t x := M62.speed_pos F0 c hc0 ht x
  let sigma0 : Real × Real → W := fun z =>
    (curveSpeed F0 c z.2 z.1)⁻¹ • deriv (fun y => e (c y z.2)) z.1
  have hsigma0 : ContinuousOn sigma0 (univ ×ˢ Icc alpha S) :=
    (hspeedC.inv₀ (fun z hz => (hvpos z.2 hz.2 z.1).ne')).smul hdata.2.2.2.1
  have hsigmarep (t : Real) (ht : t ∈ Icc alpha S) (x : Real) :
      sigma0 (x, t) = mfderiv (𝓡 n) 𝓘(Real, W) e (c x t)
        (spatialUnitTangent F0 c t x) := by
    dsimp only [sigma0]
    rw [(hdata.2.1 t ht x).deriv, spatialUnitTangent, map_smul]
  have hsigmaper (t : Real) (ht : t ∈ C) :
      Function.Periodic (fun x => sigma0 (x, t)) curvePeriod := by
    intro x
    dsimp only [sigma0]
    rw [M62.speed_periodic F0 c hc0 (hC ht) x, hderivper (hrper t (hC ht)) x]
  obtain ⟨s0, hs0, hsrep⟩ := descend C sigma0
    (hsigma0.mono (prod_mono Subset.rfl hC)) hsigmaper
  let sigma : Path := ⟨fun t => s0 t, hs0.domRestrict⟩
  obtain ⟨hHper, hHcont, _hHsmooth⟩ := embeddedCurvature_closed_periodic_data F0 c haS hc0 he
  obtain ⟨h0, hh0, hHrep⟩ := descend C (A 0)
    (hHcont.mono (prod_mono Subset.rfl hC)) (fun t ht => hHper t (hC ht))
  let H : Path := ⟨fun t => h0 t, hh0.domRestrict⟩
  let v : C(C, XR) := ⟨fun t =>
    ⟨(M62.speed_periodic F0 c hc0 (hC t.property)).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (hspeedC.comp_continuous (continuous_id.prodMk continuous_const)
          (fun _ => ⟨mem_univ _, hC t.property⟩))⟩, by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : C × Real => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    change Continuous (fun p : C × Real =>
      (M62.speed_periodic F0 c hc0 (hC p.1.property)).lift (p.2 : AddCircle curvePeriod))
    simpa only [Function.Periodic.lift_coe, Function.comp_def] using!
      hspeedC.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, hC p.1.2⟩)⟩
  have hvrep (t : C) (x : Real) : v t (x : AddCircle curvePeriod) = curveSpeed F0 c t x := by
    change (M62.speed_periodic F0 c hc0 (hC t.property)).lift (x : AddCircle curvePeriod) = _
    exact Function.Periodic.lift_coe _ x
  have hvpositive (t : C) (z : AddCircle curvePeriod) : 0 < v t z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hvrep]
    exact hvpos t (hC t.property) x
  let iv : C(C, XR) := ⟨fun t => ⟨fun z => (v t z)⁻¹,
    (v t).continuous.inv₀ (fun z => (hvpositive t z).ne')⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact v.uncurry.continuous.inv₀ (fun z => (hvpositive z.1 z.2).ne')⟩
  let V : Real := ‖v‖
  have hV : 0 ≤ V := norm_nonneg v
  have hvbound (t : C) (x : Real) : curveSpeed F0 c t x ≤ V := by
    rw [← hvrep]
    exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm (v t)
      (x : AddCircle curvePeriod)).trans (ContinuousMap.norm_coe_le_norm v t))
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  choose K hK hKbound using hjets
  obtain ⟨G, hG, hGbound⟩ := hgradient
  let bound (i : Nat) := G * (E2 * K i + E1 * K (i + 1)) +
    V ^ 2 * (E3 * K i + E2 * K 0 * K i + 2 * E2 * K (i + 1) + E1 * K (i + 2))
  have hbound (i : Nat) : 0 ≤ bound i := by
    dsimp only [bound]
    exact add_nonneg
      (mul_nonneg hG (add_nonneg (mul_nonneg hE2 (hK i))
        (mul_nonneg hE1 (hK (i + 1)))))
      (mul_nonneg (sq_nonneg V)
        (add_nonneg (add_nonneg (add_nonneg (mul_nonneg hE3 (hK i))
          (mul_nonneg (mul_nonneg hE2 (hK 0)) (hK i)))
          (mul_nonneg (mul_nonneg (by norm_num) hE2) (hK (i + 1))))
          (mul_nonneg hE1 (hK (i + 2)))))
  have hsecond (i : Nat) (t : Real) (ht : t ∈ Ioo tau S) (x : Real) :
      ‖deriv (deriv (fun y => A i (y, t))) x‖ ≤ bound i := by
    have ht0 : t ∈ Ioo alpha S := ⟨hat.trans ht.1, ht.2⟩
    have htf : t ∈ Icc a b := hsubF (Ioo_subset_Icc_self ht0)
    have hb := embeddedCurvatureJet_second_spatial_derivative_bound F0 c hc0 he i ht0 x
      hE1 hE2 hE3 (fun Z => (hE t htf (c x t) Z 0 0).1)
      (fun Z Q => (hE t htf (c x t) Z Q 0).2.1)
      (fun Z Q P => (hE t htf (c x t) Z Q P).2.2)
    have hv : curveSpeed F0 c t x ≤ V := hvbound ⟨t, ht.1.le, ht.2.le⟩ x
    have hv0 : 0 ≤ curveSpeed F0 c t x := (hvpos t (Ioo_subset_Icc_self ht0) x).le
    have hkb (k : Nat) : (F0.metric t).tangentNorm (c x t)
        (m63CurvatureJet F0 c k t x) ≤ K k := by
      rw [hjet0]
      exact hKbound k t ht x
    have hk : m62Curvature F0 c t x ≤ K 0 := hkb 0
    have hk0 : 0 ≤ m62Curvature F0 c t x := Real.sqrt_nonneg _
    have hni (k : Nat) : 0 ≤ (F0.metric t).tangentNorm (c x t)
        (m63CurvatureJet F0 c k t x) := Real.sqrt_nonneg _
    have hE2K0 : 0 ≤ E2 * K 0 := mul_nonneg hE2 (hK 0)
    have hlin : 0 ≤ E2 * (F0.metric t).tangentNorm (c x t)
        (m63CurvatureJet F0 c i t x) + E1 * (F0.metric t).tangentNorm (c x t)
          (m63CurvatureJet F0 c (i + 1) t x) :=
      add_nonneg (mul_nonneg hE2 (hni i)) (mul_nonneg hE1 (hni (i + 1)))
    have hquad : 0 ≤ E3 * (F0.metric t).tangentNorm (c x t)
        (m63CurvatureJet F0 c i t x) + E2 * m62Curvature F0 c t x *
          (F0.metric t).tangentNorm (c x t) (m63CurvatureJet F0 c i t x) +
        2 * E2 * (F0.metric t).tangentNorm (c x t) (m63CurvatureJet F0 c (i + 1) t x) +
        E1 * (F0.metric t).tangentNorm (c x t) (m63CurvatureJet F0 c (i + 2) t x) :=
      add_nonneg (add_nonneg (add_nonneg (mul_nonneg hE3 (hni i))
        (mul_nonneg (mul_nonneg hE2 hk0) (hni i)))
        (mul_nonneg (mul_nonneg (by norm_num) hE2) (hni (i + 1))))
        (mul_nonneg hE1 (hni (i + 2)))
    apply hb.trans
    dsimp only [bound]
    gcongr <;> first
      | exact hlin
      | exact hquad
      | exact hni i
      | exact hGbound t ht x
      | exact hv
      | exact hk
      | exact hkb i
      | exact hkb (i + 1)
      | exact hkb (i + 2)
  let B := fun (t : Real) (z p q : W) => coordinateHessian (F0.connection t) e (ρ z)
    (mfderiv 𝓘(Real, W) (𝓡 n) ρ z p) (mfderiv 𝓘(Real, W) (𝓡 n) ρ z q)
  have hBC : ContinuousOn
      (fun z : (Real × W) × (W × W) => B z.1.1 z.1.2 z.2.1 z.2.2)
      ((Icc alpha S ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F0 he hU hρ).continuousOn
  have hrU (t : C) (z : AddCircle curvePeriod) : r t z ∈ U := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [show r t (x : AddCircle curvePeriod) = e (c x t) from hrrep t t.property x]
    exact heU (mem_range_self _)
  let mulV (q : XR × X) : X :=
    ⟨fun z => q.1 z • q.2 z, q.1.continuous.smul q.2.continuous⟩
  have hmulV : Continuous mulV := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (XR × X) × AddCircle curvePeriod => p.1.1 p.2 • p.1.2 p.2)
    have hfirst : Continuous (fun p : (XR × X) × AddCircle curvePeriod => p.1.1 p.2) :=
      continuous_fst.fst.eval continuous_snd
    have hsecond : Continuous (fun p : (XR × X) × AddCircle curvePeriod => p.1.2 p.2) :=
      continuous_fst.snd.eval continuous_snd
    exact hfirst.smul hsecond
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  let T := Ioo tau S
  let l : Filter T := Filter.comap (Subtype.val : T → Real) (𝓝[<] S)
  have hrange : range (Subtype.val : T → Real) ∈ 𝓝[<] S := by
    simpa only [Subtype.range_coe] using Ioo_mem_nhdsLT htS
  let : l.NeBot := (inferInstance : (𝓝[<] S).NeBot).comap_of_range_mem hrange
  let : l.IsCountablyGenerated := inferInstance
  let inc : T → C := fun t => ⟨t, t.2.1.le, t.2.2.le⟩
  have hinc : Tendsto inc l (𝓝 endTime) := by
    apply tendsto_subtype_rng.mpr
    exact (tendsto_comap : Tendsto (Subtype.val : T → Real) l (𝓝[<] S)).mono_right
      nhdsWithin_le_nhds
  have hpiLim : Tendsto pi (𝓝[<] S) (𝓝 endTime) := by
    have hp : Tendsto pi (𝓝 S) (𝓝 (pi S)) := continuous_projIcc.tendsto S
    simpa only [pi, projIcc_of_mem htS.le (show S ∈ C from ⟨htS.le, le_rfl⟩)] using
      hp.mono_left nhdsWithin_le_nhds
  let State (i : Nat) := {q : Path // ∀ (t : C), (t : Real) < S → ∀ x : Real,
    q t (x : AddCircle curvePeriod) = A i (x, t)}
  have step (i : Nat) (Q : State i) : ∃ Q' : State (i + 1),
      ∀ (t : C) (x : Real), HasDerivAt (fun y : Real => Q.1 t (y : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) •
          (Q'.1 t (x : AddCircle curvePeriod) + B t (r t (x : AddCircle curvePeriod))
            (sigma t (x : AddCircle curvePeriod)) (Q.1 t (x : AddCircle curvePeriod)))) x := by
    let DX := M08.coordinatePartialS (A i)
    have hDX : ContDiffOn Real ∞ DX Ω := M08.coordinatePartialS_contDiffOn hΩ (A i) (hA i)
    have hXeq (t : Real) (ht : t ∈ Ico tau S) :
        (fun x => DX (x, t)) = deriv (fun x => A i (x, t)) :=
      funext fun x => (hdx i t ht x).deriv.symm
    have hper (t : Real) (ht : t ∈ Ico tau S) :
        Function.Periodic (fun x => DX (x, t)) curvePeriod := by
      rw [hXeq t ht]
      apply hderivper
      intro x
      change A i (x + curvePeriod, t) = A i (x, t)
      erw [← Q.2 ⟨t, ht.1, ht.2.le⟩ ht.2 (x + curvePeriod),
        ← Q.2 ⟨t, ht.1, ht.2.le⟩ ht.2 x, AddCircle.coe_add_period]
    obtain ⟨df, hdf, hdfrep⟩ := descend (Ico tau S) DX
      (hDX.continuousOn.mono (fun z hz => ⟨mem_univ _, htime z.2 hz.2⟩)) hper
    have hder (t : T) (x : Real) : HasDerivAt
        (fun y : Real => Q.1 (inc t) (y : AddCircle curvePeriod))
        (df t (x : AddCircle curvePeriod)) x := by
      rw [hdfrep t ⟨t.2.1.le, t.2.2⟩]
      exact (hdx i t ⟨t.2.1.le, t.2.2⟩ x).congr_of_eventuallyEq
        (Eventually.of_forall (Q.2 (inc t) t.2.2))
    have hLip (t : T) : LipschitzWith (⟨bound i, hbound i⟩ : NNReal)
        (fun x : Real => df t (x : AddCircle curvePeriod)) := by
      have hs : ContDiff Real ∞ (fun x => DX (x, t)) :=
        hDX.comp_contDiff (contDiff_id.prodMk contDiff_const)
          (fun _ => ⟨mem_univ _, htime t ⟨t.2.1.le, t.2.2⟩⟩)
      have heq : (fun x : Real => df t (x : AddCircle curvePeriod)) =
          fun x => DX (x, t) := funext (hdfrep t ⟨t.2.1.le, t.2.2⟩)
      rw [heq]
      apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp))
      intro x
      change ‖deriv (fun y => DX (y, t)) x‖ ≤ bound i
      rw [hXeq t ⟨t.2.1.le, t.2.2⟩]
      exact hsecond i t t.property x
    obtain ⟨dg, hdg, hderg⟩ := exists_periodic_derivative_limit_along_filter l
      (fun t => Q.1 (inc t)) (fun t => df t) (Q.1 endTime) hder hLip
      (Q.1.continuous.tendsto endTime |>.comp hinc)
    have hdgReal : Tendsto df (𝓝[<] S) (𝓝 dg) :=
      (tendsto_comap'_iff hrange).mp hdg
    let coefficientInput : C × AddCircle curvePeriod → (Real × W) × (W × W) :=
      fun z => ((z.1.1, r z.1 z.2), (sigma z.1 z.2, Q.1 z.1 z.2))
    have hinput : Continuous coefficientInput :=
      ((continuous_subtype_val.comp continuous_fst).prodMk r.uncurry.continuous).prodMk
        (sigma.uncurry.continuous.prodMk Q.1.uncurry.continuous)
    let Bq : Path := (⟨fun z => B z.1 (r z.1 z.2) (sigma z.1 z.2) (Q.1 z.1 z.2),
      hBC.comp_continuous (f := coefficientInput) hinput
        (fun z => ⟨⟨hC z.1.2, hrU z.1 z.2⟩, mem_univ _⟩)⟩ :
          C(C × AddCircle curvePeriod, W)).curry
    let fn : Real → X := fun t => mulV (iv (pi t), df t) - Bq (pi t)
    let gn : X := mulV (iv endTime, dg) - Bq endTime
    have hfn : ContinuousOn fn (Ico tau S) :=
      (hmulV.comp_continuousOn
        ((iv.continuous.comp continuous_projIcc).continuousOn.prodMk hdf)).sub
        (Bq.continuous.comp continuous_projIcc).continuousOn
    have hfnLim : Tendsto fn (𝓝[<] S) (𝓝 gn) :=
      ((hmulV.tendsto _).comp
        (((iv.continuous.tendsto endTime).comp hpiLim).prodMk_nhds hdgReal)).sub
        ((Bq.continuous.tendsto endTime).comp hpiLim)
    have hupdate : ContinuousOn (Function.update fn S gn) C := by
      rw [continuousOn_update_iff, Icc_sdiff_right]
      refine ⟨hfn, fun _ => ?_⟩
      rwa [nhdsWithin_Ico_eq_nhdsLT htS]
    let qnext : Path := ⟨fun t => Function.update fn S gn t, hupdate.domRestrict⟩
    have hBactual (t : C) (ht : (t : Real) < S) (x : Real) :
        B t (r t (x : AddCircle curvePeriod)) (sigma t (x : AddCircle curvePeriod))
          (Q.1 t (x : AddCircle curvePeriod)) =
          coordinateHessian (F0.connection t) e (c x t)
            (spatialUnitTangent F0 c t x) (m63CurvatureJet F0 c i t x) := by
      dsimp only [B]
      rw [show r t (x : AddCircle curvePeriod) = e (c x t) from hrrep t t.property x,
        show sigma t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(Real, W) e (c x t) (spatialUnitTangent F0 c t x) from
            (hsrep t t.property x).trans (hsigmarep t (hC t.property) x), Q.2 t ht x]
      dsimp only [A]
      erw [hleft (c x t) (spatialUnitTangent F0 c t x),
        hleft (c x t) (m63CurvatureJet F0 c i t x), hρe (c x t)]
    have hdfnext (t : C) (ht : (t : Real) < S) (x : Real) :
        df t (x : AddCircle curvePeriod) = v t (x : AddCircle curvePeriod) •
          (A (i + 1) (x, t) + B t (r t (x : AddCircle curvePeriod))
            (sigma t (x : AddCircle curvePeriod)) (Q.1 t (x : AddCircle curvePeriod))) := by
      rw [hdfrep t ⟨t.2.1, ht⟩, hvrep, hBactual t ht]
      exact (hdx i t ⟨t.2.1, ht⟩ x).unique
        (hasDerivAt_embeddedCurvatureJet_spatial F0 c hc0 he i
          (htime t ⟨t.2.1, ht⟩) x)
    have hnextrep (t : C) (ht : (t : Real) < S) (x : Real) :
        qnext t (x : AddCircle curvePeriod) = A (i + 1) (x, t) := by
      change Function.update fn S gn t (x : AddCircle curvePeriod) = _
      rw [Function.update_of_ne ht.ne]
      change (v (pi t) (x : AddCircle curvePeriod))⁻¹ • df t (x : AddCircle curvePeriod) -
        B (pi t) (r (pi t) (x : AddCircle curvePeriod))
          (sigma (pi t) (x : AddCircle curvePeriod)) (Q.1 (pi t) (x : AddCircle curvePeriod)) = _
      rw [hpi t t.property, hdfnext t ht, smul_smul,
        inv_mul_cancel₀ (hvpositive t (x : AddCircle curvePeriod)).ne', one_smul,
        add_sub_cancel_right]
    refine ⟨⟨qnext, hnextrep⟩, ?_⟩
    intro t x
    by_cases ht : (t : Real) = S
    · have hte : t = endTime := Subtype.ext ht
      subst t
      apply (hderg x).congr_deriv
      change dg (x : AddCircle curvePeriod) = v endTime (x : AddCircle curvePeriod) •
        (Function.update fn S gn S (x : AddCircle curvePeriod) +
          B S (r endTime (x : AddCircle curvePeriod)) (sigma endTime (x : AddCircle curvePeriod))
            (Q.1 endTime (x : AddCircle curvePeriod)))
      rw [Function.update_self]
      change dg (x : AddCircle curvePeriod) = v endTime (x : AddCircle curvePeriod) •
        ((v endTime (x : AddCircle curvePeriod))⁻¹ • dg (x : AddCircle curvePeriod) -
          B S (r endTime (x : AddCircle curvePeriod)) (sigma endTime (x : AddCircle curvePeriod))
            (Q.1 endTime (x : AddCircle curvePeriod)) +
          B S (r endTime (x : AddCircle curvePeriod)) (sigma endTime (x : AddCircle curvePeriod))
            (Q.1 endTime (x : AddCircle curvePeriod)))
      rw [sub_add_cancel, smul_smul,
        mul_inv_cancel₀ (hvpositive endTime (x : AddCircle curvePeriod)).ne', one_smul]
    · have hlt : (t : Real) < S := lt_of_le_of_ne t.2.2 ht
      rw [hnextrep t hlt, hvrep, hBactual t hlt]
      exact (hasDerivAt_embeddedCurvatureJet_spatial F0 c hc0 he i
        (htime t ⟨t.2.1, hlt⟩) x).congr_of_eventuallyEq
          (Eventually.of_forall (Q.2 t hlt))
  choose next hnext using step
  let initial : State 0 := ⟨H, fun t _ x => hHrep t t.property x⟩
  let seq : (i : Nat) → State i := fun i => Nat.rec (motive := State) initial
    (fun j q => next j q) i
  let η : Nat → Path := fun i => (seq i).1
  have hrec (i : Nat) (t : C) (x : Real) :
      HasDerivAt (fun y : Real => η i t (y : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) •
          (η (i + 1) t (x : AddCircle curvePeriod) + B t (r t (x : AddCircle curvePeriod))
            (sigma t (x : AddCircle curvePeriod)) (η i t (x : AddCircle curvePeriod)))) x :=
    hnext i (seq i) t x
  have hid := curvatureJet_identification_of_embedded_recurrences F0 hat htS le_rfl
    he hU heU hρ hρe (c2_restrict (m63C2_of_m62 hc0) hC) η
    (fun t x => hHrep t t.property x) (by
      intro i t x
      have hd := hrec i t x
      rw [hvrep, show r t (x : AddCircle curvePeriod) = e (c x t) from hrrep t t.property x,
        show sigma t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(Real, W) e (c x t) (spatialUnitTangent F0 c t x) from
            (hsrep t t.property x).trans (hsigmarep t (hC t.property) x)] at hd
      exact hd)
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · simpa only [hjet0] using hid.1
  · intro i t x
    have hd := hrec i t x
    have hb : B t (r t (x : AddCircle curvePeriod)) (sigma t (x : AddCircle curvePeriod))
        (η i t (x : AddCircle curvePeriod)) =
        coordinateHessian (F0.connection t) e (c x t)
          (spatialUnitTangent F0 c t x) (m63CurvatureJet F0 c i t x) := by
      dsimp only [B]
      rw [show r t (x : AddCircle curvePeriod) = e (c x t) from hrrep t t.property x,
        show sigma t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(Real, W) e (c x t) (spatialUnitTangent F0 c t x) from
            (hsrep t t.property x).trans (hsigmarep t (hC t.property) x), hid.1 i t x]
      erw [hleft (c x t) (spatialUnitTangent F0 c t x),
        hleft (c x t) (m63CurvatureJet F0 c i t x), hρe (c x t)]
    rw [hvrep, hb] at hd
    change HasDerivAt (fun y : Real => η i t (y : AddCircle curvePeriod))
      (curveSpeed F c t x • (η (i + 1) t (x : AddCircle curvePeriod) +
        coordinateHessian (F.connection t) e (c x t)
          (spatialUnitTangent F c t x) (m63CurvatureJet F0 c i t x))) x at hd
    simpa only [hjet0] using hd
  · simpa only [hjet0] using hid.2.1
  · simpa only [hjet0] using hid.2.2

end PoincareConjecture.M63
