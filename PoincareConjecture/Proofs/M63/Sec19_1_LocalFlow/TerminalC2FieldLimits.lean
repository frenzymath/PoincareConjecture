import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TerminalC2SpeedJetBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureTime
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedJetLimits
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicDerivativeFilterLimit
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.UniformSpace.Cauchy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral NNReal

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)

theorem exists_terminal_c2_fields
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {alpha tau T : ℝ} (haa : a ≤ alpha) (hat : alpha < tau)
    (htT : tau < T) (hTb : T ≤ b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (hρe : ∀ p, ρ (e p) = p)
    {c : ℝ → ℝ → M}
    (hsmooth : ∀ s, s ∈ Ioo alpha T → M63SmoothShrinkingCurveOn F c (Icc alpha s))
    {K R m V G J1 J2 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hm : 0 < m)
    (hV : 0 ≤ V) (hG : 0 ≤ G) (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hcurv : ∀ t, t ∈ Ioo alpha T → ∀ x, m62CurvatureSquared F c t x ≤ R)
    (hspeed : ∀ t, t ∈ Ico alpha T → ∀ x,
      m ≤ curveSpeed F c t x ∧ curveSpeed F c t x ≤ V)
    (hgradient : ∀ t, t ∈ Ico alpha T → ∀ x, |deriv (curveSpeed F c t) x| ≤ G)
    (hjets : ∀ t, t ∈ Ico tau T → ∀ x,
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤ J1 ∧
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 2 t x) ≤ J2)
    (hprimitive : ∀ t, t ∈ Ico alpha T → ∀ x,
      IntervalIntegrable (fun r => deriv (fun y =>
        m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) volume alpha t ∧
      deriv (curveSpeed F c t) x = -curveSpeed F c t x *
        ∫ r in alpha..t, deriv (fun y =>
          m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) :
    ∃ r s h : C(Icc tau T, X), ∃ v g : C(Icc tau T, XR),
      (∀ (t : Icc tau T), (t : ℝ) < T → ∀ x : ℝ,
        r t (x : AddCircle curvePeriod) = e (c x t) ∧
        s t (x : AddCircle curvePeriod) =
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) : W) ∧
        h t (x : AddCircle curvePeriod) =
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) : W) ∧
        v t (x : AddCircle curvePeriod) = curveSpeed F c t x ∧
        g t (x : AddCircle curvePeriod) = deriv (curveSpeed F c t) x) ∧
      (∀ (t : Icc tau T) z, r t z ∈ range e) ∧
      (∀ (t : Icc tau T) z, m ≤ v t z) ∧
      (∀ (t : Icc tau T) (x : ℝ), HasDerivAt
        (fun y : ℝ => r t (y : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)) x) ∧
      (∀ (t : Icc tau T) (x : ℝ), HasDerivAt
        (fun y : ℝ => v t (y : AddCircle curvePeriod) • s t (y : AddCircle curvePeriod))
        (HAdd.hAdd (α := W) (β := W) (γ := W)
          (g t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod))
          (v t (x : AddCircle curvePeriod) ^ 2 • HAdd.hAdd (α := W) (β := W) (γ := W)
            (h t (x : AddCircle curvePeriod))
            (coordinateHessian (F.connection t) e (ρ (r t (x : AddCircle curvePeriod)))
              (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                (s t (x : AddCircle curvePeriod)))
              (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                (s t (x : AddCircle curvePeriod)))))) x) ∧
      ∀ (t : Icc tau T) (x : ℝ), HasDerivAt
        (fun y : ℝ => v t (y : AddCircle curvePeriod)) (g t (x : AddCircle curvePeriod)) x := by
  classical
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  let J := Ico tau T
  let C := Icc tau T
  let Ω : Set (ℝ × ℝ) := univ ×ˢ Ioo alpha T
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have htime (t : ℝ) (ht : t ∈ J) : t ∈ Ioo alpha T := ⟨hat.trans_le ht.1, ht.2⟩
  have hsub (s : ℝ) (hs : s ∈ Ioo alpha T) : Icc alpha s ⊆ Icc a b :=
    Icc_subset_Icc haa (hs.2.le.trans hTb)
  let Fs (s : ℝ) (hs : s ∈ Ioo alpha T) :=
    m63RestrictClosedFlow F alpha s (hsub s hs) hs.1
  have hcs (s : ℝ) (hs : s ∈ Ioo alpha T) : M62ShrinkingCurve (Fs s hs) c :=
    m63SmoothRestriction (hsmooth s hs) alpha s Subset.rfl hs.1
  have hcut (t : ℝ) (ht : t ∈ Ioo alpha T) : ∃ s, s ∈ Ioo alpha T ∧ t < s := by
    refine ⟨(t + T) / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith [ht.1, ht.2]
  have hjetEq (s : ℝ) (hs : s ∈ Ioo alpha T) (i : ℕ) (t x : ℝ) :
      m63CurvatureJet (Fs s hs) c i t x = m63CurvatureJet F c i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F c t (fun y => m63CurvatureJet (Fs s hs) c i t y) x =
        m62SpatialDerivative F c t (fun y => m63CurvatureJet F c i t y) x
      rw [show (fun y => m63CurvatureJet (Fs s hs) c i t y) =
        (fun y => m63CurvatureJet F c i t y) from funext ih]
  let A : ℝ × ℝ → W := fun z => e (c z.1 z.2)
  let H : ℝ × ℝ → W := fun z =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.1 z.2) (m62CurvatureVector F c z.2 z.1)
  let vv : ℝ × ℝ → ℝ := fun z => curveSpeed F c z.2 z.1
  let gg : ℝ × ℝ → ℝ := fun z => deriv (curveSpeed F c z.2) z.1
  let N : ℝ × ℝ → ℝ := fun z => m62TangentRicci F c z.2 z.1 +
    m62CurvatureSquared F c z.2 z.1
  have hA : ContDiffOn ℝ ∞ A Ω := by
    intro z hz
    obtain ⟨s, hs, hts⟩ := hcut z.2 hz.2
    exact (((he.comp_contMDiffOn (hcs s hs).joint_smooth).contDiffOn).contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz.2.1, hts⟩)).contDiffWithinAt
  have hpush : ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun p : TangentBundle (𝓡 n) M => (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).comp
      (he.contMDiff_tangentMap (by simp))
  have hH : ContDiffOn ℝ ∞ H Ω := by
    intro z hz
    obtain ⟨s, hs, hts⟩ := hcut z.2 hz.2
    exact ((hpush.comp_contMDiffOn (curvatureJet_joint_contMDiff
      (Fs s hs) c (hcs s hs) 0)).contDiffOn.contDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz.2.1, hts⟩)).contDiffWithinAt
  have hv : ContDiffOn ℝ ∞ vv Ω := by
    intro z hz
    obtain ⟨s, hs, hts⟩ := hcut z.2 hz.2
    exact ((speed_joint_contDiffOn (Fs s hs) c (hcs s hs)).contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz.2.1, hts⟩)).contDiffWithinAt
  have hN : ContDiffOn ℝ ∞ N Ω := by
    intro z hz
    obtain ⟨s, hs, hts⟩ := hcut z.2 hz.2
    exact ((normalization_coefficient_contDiffOn (Fs s hs) c (hcs s hs)).contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz.2.1, hts⟩)).contDiffWithinAt
  have hvdx (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) :
      HasDerivAt (curveSpeed F c t) (M08.coordinatePartialS vv (x, t)) x :=
    M08.coordinateSlice_fst_hasDerivAt vv (p := (x, t))
      ((hv.contDiffAt (hΩ.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp))
  have hg : ContDiffOn ℝ ∞ gg Ω :=
    (M08.coordinatePartialS_contDiffOn hΩ vv hv).congr
      (fun z hz => (hvdx z.2 hz.2 z.1).deriv)
  let P : ℝ × ℝ → W := fun z => deriv (fun y => A (y, z.2)) z.1
  have hP : ContDiffOn ℝ ∞ P Ω :=
    (M08.coordinatePartialS_contDiffOn hΩ A hA).congr (fun z hz =>
      (M08.coordinateSlice_fst_hasDerivAt A (p := z)
        ((hA.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))).deriv)
  let I : ℝ × ℝ → ℝ := fun z => -gg z / vv z
  have hvpos (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) : 0 < vv (x, t) :=
    hm.trans_le (hspeed t (Ioo_subset_Ico_self ht) x).1
  have hI : ContDiffOn ℝ ∞ I Ω := hg.neg.div hv (fun z hz => (hvpos z.2 hz.2 z.1).ne')
  have hIeq (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) :
      I (x, t) = ∫ u in alpha..t, deriv (fun y => N (y, u)) x := by
    have hf := (hprimitive t (Ioo_subset_Ico_self ht) x).2
    dsimp only [I, gg, vv, N]
    rw [hf]
    have hv0 : curveSpeed F c t x ≠ 0 := (hvpos t ht x).ne'
    field_simp [hv0]
  let Q : ℝ × ℝ → W × W × ℝ × ℝ := fun z => (A z, H z, vv z, I z)
  have hQ : ContDiffOn ℝ ∞ Q Ω := hA.prodMk (hH.prodMk (hv.prodMk hI))
  have hderivper {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → E} (hf : Function.Periodic f curvePeriod) :
      Function.Periodic (deriv f) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun g : ℝ → E => deriv g x) (funext hf)
  have hper (t : ℝ) (ht : t ∈ J) :
      Function.Periodic (fun x => Q (x, t)) curvePeriod := by
    obtain ⟨s, hs, hts⟩ := hcut t (htime t ht)
    have htc : t ∈ Icc alpha s := ⟨(htime t ht).1.le, hts.le⟩
    have hh := (embeddedCurvature_closed_periodic_data (Fs s hs) c hs.1 (hcs s hs) he).1
    have hvs := speed_periodic (Fs s hs) c (hcs s hs) htc
    have hgs : Function.Periodic (deriv (curveSpeed F c t)) curvePeriod := by
      intro x
      rw [← deriv_comp_add_const]
      exact congrArg (fun f : ℝ → ℝ => deriv f x) (funext hvs)
    intro x
    apply Prod.ext
    · exact congrArg e ((hcs s hs).periodic t htc x)
    · apply Prod.ext
      · exact hh t htc x
      · exact Prod.ext (hvs x) (congrArg₂ (fun y z : ℝ => -y / z) (hgs x) (hvs x))
  have descend {E : Type v} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
      (hf : ContinuousOn f (univ ×ˢ J))
      (hper : ∀ t ∈ J, Function.Periodic (fun x => f (x, t)) curvePeriod) :
      ∃ q : ℝ → C(AddCircle curvePeriod, E), ContinuousOn q J ∧
        ∀ t ∈ J, ∀ x : ℝ, q t (x : AddCircle curvePeriod) = f (x, t) := by
    let q : ℝ → C(AddCircle curvePeriod, E) := fun t => if ht : t ∈ J then
      ⟨(hper t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
          (hf.comp_continuous (continuous_id.prodMk continuous_const)
            (fun _ => ⟨mem_univ _, ht⟩))⟩ else 0
    have hq (t : ℝ) (ht : t ∈ J) (x : ℝ) : q t (x : AddCircle curvePeriod) = f (x, t) := by
      simp only [q, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    refine ⟨q, continuousOn_iff_continuous_domRestrict.mpr ?_, hq⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : J × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    exact (hf.comp_continuous
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨mem_univ _, p.1.2⟩)).congr (fun p => (hq p.1 p.1.2 p.2).symm)
  have hJΩ : univ ×ˢ J ⊆ Ω := fun z hz => ⟨mem_univ _, htime z.2 hz.2⟩
  obtain ⟨q, hq, hqrep⟩ := descend Q (hQ.continuousOn.mono hJΩ) hper
  obtain ⟨p, hp, hprep⟩ := descend P (hP.continuousOn.mono hJΩ) (fun t ht => by
    have hAp : Function.Periodic (fun x => A (x, t)) curvePeriod :=
      fun x => congrArg Prod.fst (hper t ht x)
    exact hderivper hAp)
  obtain ⟨E1, E2, _E3, ⟨hE1, hE2, _hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let k := Real.sqrt R
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hkcap (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) : m62Curvature F c t x ≤ k :=
    Real.sqrt_le_sqrt (hcurv t ht x)
  let CR := E1 * k
  let CH := E2 * k ^ 2 + E1 * (J2 + 2 * k ^ 3 + (K + 4 * K) * k + 4 * K + 2 * k * J1)
  let CV := (K + R) * V
  let CI := V * (K + 2 * K * k + 2 * k * J1)
  let CQ := CR + CH + CV + CI
  have hCR : 0 ≤ CR := mul_nonneg hE1 hk
  have hCH : 0 ≤ CH := by dsimp only [CH]; positivity
  have hCV : 0 ≤ CV := mul_nonneg (add_nonneg hK hR) hV
  have hCI : 0 ≤ CI := by dsimp only [CI]; positivity
  have hCQ : 0 ≤ CQ := by dsimp only [CQ]; positivity
  have hqt (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      DifferentiableAt ℝ (fun u => Q (x, u)) t ∧ ‖deriv (fun u => Q (x, u)) t‖ ≤ CQ := by
    obtain ⟨s, hs, hts⟩ := hcut t (htime t ht)
    have hto : t ∈ Ioo alpha s := ⟨(htime t ht).1, hts⟩
    have htc := Ioo_subset_Icc_self hto
    have htf := hsub s hs htc
    have hBs := m63RestrictAmbientBounds hBounds alpha s (hsub s hs) hs.1
    have hdR := (c2ShrinkingCurve_embedded_interior_equation
      (m63C2_of_m62 (hcs s hs)) he).2 t (by simpa only [interior_Icc] using hto) x
    obtain ⟨hdH, hbH⟩ := embeddedCurvature_time_derivative_bound (Fs s hs) c (hcs s hs) he
      hK hK hK hBs hto x hE1 hE2
      (fun Y => (hE t htf (c x t) Y 0 0).1)
      (fun Y Z => (hE t htf (c x t) Y Z 0).2.1)
    have hdV := hasDerivAt_speed (Fs s hs) c (hcs s hs) hto x
    let Nx : ℝ → ℝ := fun u => deriv (fun y => N (y, u)) x
    have hNx : ContinuousOn Nx (Ioo alpha T) := by
      apply ((M08.coordinatePartialS_contDiffOn hΩ N hN).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨mem_univ _, hu⟩)).congr
      · intro u hu
        exact (M08.coordinateSlice_fst_hasDerivAt N (p := (x, u))
          ((hN.contDiffAt (hΩ.mem_nhds ⟨mem_univ _, hu⟩)).differentiableAt (by simp))).deriv
    have hdI := intervalIntegral.integral_hasDerivAt_right
      (hprimitive t (Ioo_subset_Ico_self (htime t ht)) x).1
      (hNx.stronglyMeasurableAtFilter isOpen_Ioo t (htime t ht))
      (hNx.continuousAt (isOpen_Ioo.mem_nhds (htime t ht)))
    have hdI' : HasDerivAt (fun u => I (x, u)) (Nx t) t :=
      hdI.congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioo.mem_nhds (htime t ht)] with u hu
        exact hIeq u hu x)
    have hd := hdR.prodMk (hdH.prodMk (hdV.prodMk hdI'))
    change HasDerivAt (fun u => Q (x, u)) _ t at hd
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    have hbR : ‖H (x, t)‖ ≤ CR :=
      ((hE t htf (c x t) (m62CurvatureVector F c t x) 0 0).1).trans
        (mul_le_mul_of_nonneg_left (hkcap t (htime t ht) x) hE1)
    have hbH' := hbH.trans (show
        E2 * m62Curvature (Fs s hs) c t x ^ 2 + E1 *
          ((F.metric t).tangentNorm (c x t) (m63CurvatureJet (Fs s hs) c 2 t x) +
            2 * m62Curvature (Fs s hs) c t x ^ 3 +
            (K + 4 * K) * m62Curvature (Fs s hs) c t x + 4 * K +
            2 * m62Curvature (Fs s hs) c t x *
              (F.metric t).tangentNorm (c x t) (m63CurvatureJet (Fs s hs) c 1 t x)) ≤ CH from by
      rw [hjetEq s hs, hjetEq s hs]
      have hkr : m62Curvature (Fs s hs) c t x ≤ k := hkcap t (htime t ht) x
      have hur := (hjets t ht x).1
      have hwr := (hjets t ht x).2
      have hk0 : 0 ≤ m62Curvature (Fs s hs) c t x := curvature_nonneg F c t x
      have hu0 : 0 ≤ (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) :=
        Real.sqrt_nonneg _
      dsimp only [CH]
      gcongr)
    have hunit := (unitTangent_norm (Fs s hs) c (hcs s hs) htc x).le
    have hRic : |m62TangentRicci F c t x| ≤ K :=
      hBounds.ricci t htf (c x t) (spatialUnitTangent F c t x)
        (spatialUnitTangent F c t x) hunit hunit
    have hbV : |-(N (x, t)) * vv (x, t)| ≤ CV := by
      rw [abs_mul, abs_neg, abs_of_pos (hvpos t (htime t ht) x)]
      apply mul_le_mul _ (hspeed t (Ioo_subset_Ico_self (htime t ht)) x).2
        (speed_nonneg F c t x) (add_nonneg hK hR)
      exact (abs_add_le _ _).trans (add_le_add hRic
        (by rw [abs_of_nonneg (curvatureSquared_nonneg F c t x)]; exact hcurv t (htime t ht) x))
    have hbI : |Nx t| ≤ CI := by
      have hb := normalizationCoefficient_spatial_abs_bound (Fs s hs) c (hcs s hs) hBs hto x
      rw [hjetEq s hs] at hb
      apply hb.trans
      have hvr : curveSpeed (Fs s hs) c t x ≤ V :=
        (hspeed t (Ioo_subset_Ico_self (htime t ht)) x).2
      have hkr : m62Curvature (Fs s hs) c t x ≤ k := hkcap t (htime t ht) x
      have hur : ((Fs s hs).metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤ J1 :=
        (hjets t ht x).1
      have hv0 : 0 ≤ curveSpeed (Fs s hs) c t x := speed_nonneg F c t x
      have hk0 : 0 ≤ m62Curvature (Fs s hs) c t x := curvature_nonneg F c t x
      have hu0 : 0 ≤ ((Fs s hs).metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) :=
        Real.sqrt_nonneg _
      dsimp only [CI]
      gcongr
    simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨hbR.trans (by dsimp only [CQ]; linarith),
      hbH'.trans (by dsimp only [CQ]; linarith),
      hbV.trans (by dsimp only [CQ]; linarith), hbI.trans (by dsimp only [CQ]; linarith)⟩
  have hqlip : LipschitzOnWith ⟨CQ, hCQ⟩ q J := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    apply (ContinuousMap.dist_le (mul_nonneg hCQ dist_nonneg)).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hqrep t ht, hqrep u hu]
    exact ((convex_Ico tau T).lipschitzOnWith_of_nnnorm_deriv_le (C := ⟨CQ, hCQ⟩)
      (fun w hw => (hqt w hw x).1) (fun w hw => (hqt w hw x).2)).dist_le_mul t ht u hu
  have hqend : ∃ qT, Tendsto q (𝓝[<] T) (𝓝 qT) :=
    cauchy_map_iff_exists_tendsto.mp (((cauchy_nhds (a := T)).mono
      (show 𝓝[<] T ≤ 𝓝 T from inf_le_left)).map_of_le
      hqlip.uniformContinuousOn (le_principal_iff.mpr (Ico_mem_nhdsLT htT)))
  have close {E : Type v} [NormedAddCommGroup E] [CompleteSpace E]
      (f : ℝ → C(AddCircle curvePeriod, E)) (hf : ContinuousOn f J)
      (hl : ∃ fT, Tendsto f (𝓝[<] T) (𝓝 fT)) :
      ∃ fbar : C(C, C(AddCircle curvePeriod, E)),
        (∀ t (ht : t ∈ J), fbar ⟨t, Ico_subset_Icc_self ht⟩ = f t) ∧
        Tendsto f (𝓝[<] T) (𝓝 (fbar ⟨T, htT.le, le_rfl⟩)) := by
    obtain ⟨fT, hlim⟩ := hl
    have hc : ContinuousOn (extendFrom J f) C := by
      apply continuousOn_extendFrom (by rw [closure_Ico htT.ne])
      intro t ht
      rcases ht.2.eq_or_lt with h | h
      · subst t
        exact ⟨fT, by simpa only [J, nhdsWithin_Ico_eq_nhdsLT htT] using hlim⟩
      · exact ⟨f t, hf t ⟨ht.1, h⟩⟩
    refine ⟨⟨fun t => extendFrom J f t, hc.domRestrict⟩,
      fun t ht => extendFrom_extends hf t ht, ?_⟩
    have heq : extendFrom J f T = fT := extendFrom_eq
      (by rw [closure_Ico htT.ne]; exact ⟨htT.le, le_rfl⟩)
      (by simpa only [J, nhdsWithin_Ico_eq_nhdsLT htT] using hlim)
    simpa only [ContinuousMap.coe_mk, heq] using hlim
  obtain ⟨qbar, hqbar, _hqlim⟩ := close q hq hqend
  let r : C(C, X) := (⟨fun z : C × AddCircle curvePeriod => (qbar z.1 z.2).1,
    qbar.uncurry.continuous.fst⟩ : C(C × AddCircle curvePeriod, W)).curry
  let h : C(C, X) := (⟨fun z : C × AddCircle curvePeriod => (qbar z.1 z.2).2.1,
    qbar.uncurry.continuous.snd.fst⟩ : C(C × AddCircle curvePeriod, W)).curry
  let v : C(C, XR) := (⟨fun z : C × AddCircle curvePeriod => (qbar z.1 z.2).2.2.1,
    qbar.uncurry.continuous.snd.snd.fst⟩ : C(C × AddCircle curvePeriod, ℝ)).curry
  let ip : C(C, XR) := (⟨fun z : C × AddCircle curvePeriod => (qbar z.1 z.2).2.2.2,
    qbar.uncurry.continuous.snd.snd.snd⟩ : C(C × AddCircle curvePeriod, ℝ)).curry
  let g : C(C, XR) := (⟨fun z : C × AddCircle curvePeriod => -v z.1 z.2 * ip z.1 z.2,
    v.uncurry.continuous.neg.mul ip.uncurry.continuous⟩ :
      C(C × AddCircle curvePeriod, ℝ)).curry
  have hrep (t : C) (ht : (t : ℝ) < T) (x : ℝ) :
      r t (x : AddCircle curvePeriod) = A (x, t) ∧
      h t (x : AddCircle curvePeriod) = H (x, t) ∧
      v t (x : AddCircle curvePeriod) = vv (x, t) ∧
      g t (x : AddCircle curvePeriod) = gg (x, t) := by
    have htJ : (t : ℝ) ∈ J := ⟨t.2.1, ht⟩
    have heq : qbar t (x : AddCircle curvePeriod) = Q (x, t) := by
      rw [hqbar t htJ, hqrep t htJ]
    change (qbar t (x : AddCircle curvePeriod)).1 = _ ∧
      (qbar t (x : AddCircle curvePeriod)).2.1 = _ ∧
      (qbar t (x : AddCircle curvePeriod)).2.2.1 = _ ∧
      -(qbar t (x : AddCircle curvePeriod)).2.2.1 *
        (qbar t (x : AddCircle curvePeriod)).2.2.2 = _
    rw [heq]
    refine ⟨rfl, rfl, rfl, ?_⟩
    change -vv (x, t) * (-gg (x, t) / vv (x, t)) = gg (x, t)
    field_simp [(hvpos t (htime t htJ) x).ne']
  let endTime : C := ⟨T, htT.le, le_rfl⟩
  let ti : ℝ → C := fun u => if hu : u ∈ J then ⟨u, Ico_subset_Icc_self hu⟩ else
    ⟨tau, le_rfl, htT.le⟩
  have hti (u : ℝ) : (ti u : ℝ) ∈ J := by
    dsimp only [ti]
    split_ifs with hu
    · exact hu
    · exact ⟨le_rfl, htT⟩
  have htieq : ∀ᶠ u in 𝓝[<] T, (ti u : ℝ) = u := by
    filter_upwards [Ico_mem_nhdsLT htT] with u hu
    simp only [ti, J, dif_pos hu]
  have htilim : Tendsto ti (𝓝[<] T) (𝓝 endTime) := by
    apply tendsto_subtype_rng.mpr
    exact (tendsto_id.mono_left inf_le_left).congr' (htieq.mono (fun _ hu => hu.symm))
  have hrange : ∀ (t : C) z, r t z ∈ range e := by
    intro t z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    by_cases ht : (t : ℝ) < T
    · rw [(hrep t ht x).1]
      exact mem_range_self _
    · have hte : t = endTime := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
      subst t
      have hclosed : IsClosed (range e) := by
        simpa only [image_univ] using (hcompact.image he.continuous).isClosed
      exact hclosed.mem_of_tendsto
        (((continuous_eval_const (x : AddCircle curvePeriod)).tendsto (r endTime)).comp
          (r.continuous.tendsto endTime |>.comp htilim))
        (Eventually.of_forall (fun u => by
          change r (ti u) (x : AddCircle curvePeriod) ∈ range e
          rw [(hrep (ti u) (hti u).2 x).1]
          exact mem_range_self _))
  have hvlow : ∀ (t : C) z, m ≤ v t z := by
    intro t z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    by_cases ht : (t : ℝ) < T
    · rw [(hrep t ht x).2.2.1]
      exact (hspeed t ⟨hat.le.trans t.2.1, ht⟩ x).1
    · have hte : t = endTime := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
      subst t
      apply ge_of_tendsto
        (((continuous_eval_const (x : AddCircle curvePeriod)).tendsto (v endTime)).comp
          (v.continuous.tendsto endTime |>.comp htilim))
      exact Eventually.of_forall (fun u => by
        change m ≤ v (ti u) (x : AddCircle curvePeriod)
        rw [(hrep (ti u) (hti u).2 x).2.2.1]
        exact (hspeed (ti u) ⟨hat.le.trans (hti u).1, (hti u).2⟩ x).1)
  let S : ℝ × ℝ → W := fun z => mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.1 z.2)
    (spatialUnitTangent F c z.2 z.1)
  let B0 : ℝ × ℝ → W := fun z => coordinateHessian (F.connection z.2) e (c z.1 z.2)
    (spatialUnitTangent F c z.2 z.1) (spatialUnitTangent F c z.2 z.1)
  let Z0 : ℝ × ℝ → W := fun z => gg z • S z + vv z ^ 2 • (H z + B0 z)
  have hfirst (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      HasDerivAt (fun y => A (y, t)) (P (x, t)) x :=
    (((hA.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, htime t ht⟩)).differentiable (by simp)) x).hasDerivAt
  have hjet (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      P (x, t) = vv (x, t) • S (x, t) ∧
      HasDerivAt (fun y => P (y, t)) (Z0 (x, t)) x := by
    obtain ⟨s, hs, hts⟩ := hcut t (htime t ht)
    have htc : t ∈ Icc alpha s := ⟨(htime t ht).1.le, hts.le⟩
    have hc2 := m63C2_of_m62 (hcs s hs)
    let v0 := curveSpeed F c t x
    let S0 := spatialUnitTangent F c t x
    have hv0 : v0 ≠ 0 := (hvpos t (htime t ht) x).ne'
    have hvel : curveVelocity (fun y => c y t) x = v0 • S0 := by
      dsimp only [S0, spatialUnitTangent]
      rw [smul_smul, mul_inv_cancel₀ hv0, one_smul]
    have hd := (c2ShrinkingCurve_embedded_closed_data hc2 he).2.1 t htc x
    rw [hvel, map_smul] at hd
    have hpval : P (x, t) = vv (x, t) • S (x, t) := hd.deriv
    refine ⟨hpval, ?_⟩
    have hscale : coordinateHessian (F.connection t) e (c x t) (v0 • S0) (v0 • S0) =
        v0 ^ 2 • coordinateHessian (F.connection t) e (c x t) S0 S0 := by
      ext i
      have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun p => e p i) :=
        (EuclideanSpace.proj i).contDiff.contMDiff.comp he
      obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hei).1 (c x t)
      have h0 (Y Q : TangentSpace (𝓡 n) (c x t)) :
          Function.update ![S0, Q] 0 Y = ![Y, Q] := by
        ext j
        fin_cases j <;> simp [Function.update]
      have h1 (Y : TangentSpace (𝓡 n) (c x t)) :
          Function.update ![S0, S0] 1 Y = ![S0, Y] := by
        ext j
        fin_cases j <;> simp [Function.update]
      have hfst : (F.connection t).hessian (fun p => e p i) (c x t) (v0 • S0) (v0 • S0) =
          v0 * (F.connection t).hessian (fun p => e p i) (c x t) S0 (v0 • S0) := by
        simpa only [h0, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, v0 • S0] 0 v0 S0
      have hsnd : (F.connection t).hessian (fun p => e p i) (c x t) S0 (v0 • S0) =
          v0 * (F.connection t).hessian (fun p => e p i) (c x t) S0 S0 := by
        simpa only [h1, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, S0] 1 v0 S0
      change (F.connection t).hessian (fun p => e p i) (c x t) (v0 • S0) (v0 • S0) =
        v0 ^ 2 * (F.connection t).hessian (fun p => e p i) (c x t) S0 S0
      rw [hfst, hsnd]
      ring
    have hacc := embedded_curvature_eq_acceleration_sub_tangent F he c
      (hc2.spatial_regular t htc) (hc2.immersed t htc) x
    rw [hvel, hscale, hd.deriv] at hacc
    have hZ : deriv (fun y => P (y, t)) x = Z0 (x, t) := by
      ext i
      have hi := congrArg (fun z : W => z i) hacc
      simp only [Z0, S, H, B0, vv, gg, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul] at hi ⊢
      change _ = deriv (curveSpeed F c t) x * _ + v0 ^ 2 * (_ + _)
      change (H (x, t)).ofLp i = (v0 ^ 2)⁻¹ *
        ((deriv (fun y => P (y, t)) x).ofLp i - v0 ^ 2 * (B0 (x, t)).ofLp i) -
        (deriv (curveSpeed F c t) x / v0 ^ 3) * (v0 * (S (x, t)).ofLp i) at hi
      field_simp [hv0] at hi
      nlinarith only [hi]
    exact (((hP.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, htime t ht⟩)).differentiable (by simp) x).hasDerivAt).congr_deriv hZ
  let L := G * E1 + V ^ 2 * (E1 * k + E2)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hpLip (t : ℝ) (ht : t ∈ J) :
      LipschitzWith ⟨L, hL⟩ (fun x : ℝ => p t (x : AddCircle curvePeriod)) := by
    have heq : (fun x : ℝ => p t (x : AddCircle curvePeriod)) = (fun x => P (x, t)) :=
      funext (hprep t ht)
    rw [heq]
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hjet t ht x).2.differentiableAt)
    intro x
    change ‖deriv (fun y => P (y, t)) x‖ ≤ L
    rw [(hjet t ht x).2.deriv]
    obtain ⟨s, hs, hts⟩ := hcut t (htime t ht)
    have htc : t ∈ Icc alpha s := ⟨(htime t ht).1.le, hts.le⟩
    have htf := hsub s hs htc
    have hunit : (F.metric t).tangentNorm (c x t) (spatialUnitTangent F c t x) = 1 :=
      unitTangent_norm (Fs s hs) c (hcs s hs) htc x
    have hSn : ‖S (x, t)‖ ≤ E1 := by
      simpa only [hunit, mul_one] using
        (hE t htf (c x t) (spatialUnitTangent F c t x) 0 0).1
    have hHn : ‖H (x, t)‖ ≤ E1 * k :=
      ((hE t htf (c x t) (m62CurvatureVector F c t x) 0 0).1).trans
        (mul_le_mul_of_nonneg_left (hkcap t (htime t ht) x) hE1)
    have hBn : ‖B0 (x, t)‖ ≤ E2 := by
      simpa only [hunit, mul_one] using
        (hE t htf (c x t) (spatialUnitTangent F c t x)
          (spatialUnitTangent F c t x) 0).2.1
    calc
      ‖Z0 (x, t)‖ ≤ |gg (x, t)| * ‖S (x, t)‖ +
          vv (x, t) ^ 2 * (‖H (x, t)‖ + ‖B0 (x, t)‖) := by
        exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul, Real.norm_eq_abs])
          ((norm_smul _ _).le.trans (by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg _))))
      _ ≤ L := add_le_add
        (mul_le_mul (hgradient t (Ioo_subset_Ico_self (htime t ht)) x) hSn (norm_nonneg _) hG)
        (mul_le_mul (pow_le_pow_left₀ (speed_nonneg F c t x)
          (hspeed t (Ioo_subset_Ico_self (htime t ht)) x).2 2)
          (add_le_add hHn hBn) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (sq_nonneg V))
  obtain ⟨pT, hplim0, hpT⟩ := exists_periodic_derivative_limit_along_filter
    (l := 𝓝[<] T) (fun u => r (ti u)) (fun u => p (ti u)) (r endTime)
    (fun u x => by
      have hd := hfirst (ti u) (hti u) x
      rw [← hprep (ti u) (hti u) x] at hd
      exact hd.congr_of_eventuallyEq
        (Eventually.of_forall (fun y => (hrep (ti u) (hti u).2 y).1)))
    (fun u => hpLip (ti u) (hti u)) (r.continuous.tendsto endTime |>.comp htilim)
  have hplim : Tendsto p (𝓝[<] T) (𝓝 pT) := hplim0.congr' (htieq.mono (fun u hu => by rw [hu]))
  obtain ⟨pbar, hpbar, hpbarlim⟩ := close p hp ⟨pT, hplim⟩
  have hpbarT : pbar endTime = pT := tendsto_nhds_unique hpbarlim hplim
  let s : C(C, X) := (⟨fun z : C × AddCircle curvePeriod => (v z.1 z.2)⁻¹ • pbar z.1 z.2,
    (v.uncurry.continuous.inv₀ (fun z => (hm.trans_le (hvlow z.1 z.2)).ne')).smul
      pbar.uncurry.continuous⟩ : C(C × AddCircle curvePeriod, W)).curry
  have hps (t : C) (z : AddCircle curvePeriod) : pbar t z = v t z • s t z := by
    change pbar t z = v t z • ((v t z)⁻¹ • pbar t z)
    rw [smul_smul, mul_inv_cancel₀ (hm.trans_le (hvlow t z)).ne', one_smul]
  have hsrep (t : C) (ht : (t : ℝ) < T) (x : ℝ) :
      s t (x : AddCircle curvePeriod) = S (x, t) := by
    have htJ : (t : ℝ) ∈ J := ⟨t.2.1, ht⟩
    change (v t (x : AddCircle curvePeriod))⁻¹ • pbar t (x : AddCircle curvePeriod) = _
    rw [(hrep t ht x).2.2.1, hpbar t htJ, hprep t htJ, (hjet t htJ x).1]
    rw [smul_smul, inv_mul_cancel₀ (hvpos t (htime t htJ) x).ne', one_smul]
  have hdr (t : C) (x : ℝ) : HasDerivAt (fun y : ℝ => r t (y : AddCircle curvePeriod))
      (pbar t (x : AddCircle curvePeriod)) x := by
    by_cases ht : (t : ℝ) < T
    · have htJ : (t : ℝ) ∈ J := ⟨t.2.1, ht⟩
      rw [hpbar t htJ, hprep t htJ]
      exact (hfirst t htJ x).congr_of_eventuallyEq
        (Eventually.of_forall (fun y => (hrep t ht y).1))
    · have hte : t = endTime := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
      subst t
      rw [hpbarT]
      exact hpT x
  let B : (ℝ × W) × (W × W) → W := fun z =>
    coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
  have hBC : ContinuousOn B ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  let input : C × AddCircle curvePeriod → (ℝ × W) × (W × W) :=
    fun z => (((z.1 : ℝ), r z.1 z.2), (s z.1 z.2, s z.1 z.2))
  have hinput : Continuous input :=
    ((continuous_subtype_val.comp continuous_fst).prodMk r.uncurry.continuous).prodMk
      (s.uncurry.continuous.prodMk s.uncurry.continuous)
  have hinputU (z : C × AddCircle curvePeriod) : input z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
    ⟨⟨⟨haa.trans (hat.le.trans z.1.2.1), z.1.2.2.trans hTb⟩,
      heU (hrange z.1 z.2)⟩, mem_univ _⟩
  let Z : C(C, X) := (⟨fun z : C × AddCircle curvePeriod =>
    g z.1 z.2 • s z.1 z.2 + v z.1 z.2 ^ 2 • (h z.1 z.2 + B (input z)),
    (g.uncurry.continuous.smul s.uncurry.continuous).add
      ((v.uncurry.continuous.pow 2).smul (h.uncurry.continuous.add
        (hBC.comp_continuous (f := input) hinput hinputU)))⟩ :
      C(C × AddCircle curvePeriod, W)).curry
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hZrep (t : C) (ht : (t : ℝ) < T) (x : ℝ) :
      Z t (x : AddCircle curvePeriod) = Z0 (x, t) := by
    change g t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod) +
      v t (x : AddCircle curvePeriod) ^ 2 • (h t (x : AddCircle curvePeriod) +
        B (((t : ℝ), r t (x : AddCircle curvePeriod)),
          (s t (x : AddCircle curvePeriod), s t (x : AddCircle curvePeriod)))) = _
    rw [(hrep t ht x).2.2.2, (hrep t ht x).2.2.1, (hrep t ht x).2.1,
      (hrep t ht x).1, hsrep t ht x]
    dsimp only [B, S, A, Z0, B0]
    rw [hleft, hρe]
  have hdP (t : C) (ht : (t : ℝ) < T) (x : ℝ) :
      HasDerivAt (fun y : ℝ => pbar t (y : AddCircle curvePeriod))
        (Z t (x : AddCircle curvePeriod)) x := by
    rw [hZrep t ht x]
    exact ((hjet t ⟨t.2.1, ht⟩ x).2).congr_of_eventuallyEq
      (Eventually.of_forall (fun y => by
        change pbar t (y : AddCircle curvePeriod) = P (y, t)
        rw [hpbar t ⟨t.2.1, ht⟩, hprep t ⟨t.2.1, ht⟩]))
  have hdv (t : C) (ht : (t : ℝ) < T) (x : ℝ) :
      HasDerivAt (fun y : ℝ => v t (y : AddCircle curvePeriod))
        (g t (x : AddCircle curvePeriod)) x := by
    rw [(hrep t ht x).2.2.2]
    exact ((hvdx t (htime t ⟨t.2.1, ht⟩) x).congr_deriv
      (hvdx t (htime t ⟨t.2.1, ht⟩) x).deriv.symm).congr_of_eventuallyEq
        (Eventually.of_forall (fun y => (hrep t ht y).2.2.1))
  have hdPend (x : ℝ) : HasDerivAt
      (fun y : ℝ => pbar endTime (y : AddCircle curvePeriod))
      (Z endTime (x : AddCircle curvePeriod)) x :=
    hasDerivAt_of_tendstoUniformly
      ((ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (Z.continuous.tendsto endTime |>.comp htilim)).comp
          (fun y : ℝ => (y : AddCircle curvePeriod)))
      (Eventually.of_forall (fun u y => hdP (ti u) (hti u).2 y))
      (fun y => (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (pbar endTime)
        |>.comp (pbar.continuous.tendsto endTime |>.comp htilim)) x
  have hdvend (x : ℝ) : HasDerivAt
      (fun y : ℝ => v endTime (y : AddCircle curvePeriod))
      (g endTime (x : AddCircle curvePeriod)) x :=
    hasDerivAt_of_tendstoUniformly
      ((ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (g.continuous.tendsto endTime |>.comp htilim)).comp
          (fun y : ℝ => (y : AddCircle curvePeriod)))
      (Eventually.of_forall (fun u y => hdv (ti u) (hti u).2 y))
      (fun y => (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (v endTime)
        |>.comp (v.continuous.tendsto endTime |>.comp htilim)) x
  refine ⟨r, s, h, v, g, ?_, hrange, hvlow, ?_, ?_, ?_⟩
  · intro t ht x
    exact ⟨(hrep t ht x).1, hsrep t ht x, (hrep t ht x).2⟩
  · intro t x
    exact (hdr t x).congr_deriv (hps t _)
  · intro t x
    have hd : HasDerivAt (fun y : ℝ => pbar t (y : AddCircle curvePeriod))
        (Z t (x : AddCircle curvePeriod)) x := by
      by_cases ht : (t : ℝ) < T
      · exact hdP t ht x
      · have hte : t = endTime := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
        subst t
        exact hdPend x
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun y => (hps t _).symm))
  · intro t x
    by_cases ht : (t : ℝ) < T
    · exact hdv t ht x
    · have hte : t = endTime := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
      subst t
      exact hdvend x

end PoincareConjecture.M63
