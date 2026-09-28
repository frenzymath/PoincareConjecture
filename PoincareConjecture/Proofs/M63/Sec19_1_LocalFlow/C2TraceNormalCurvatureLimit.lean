import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceInitialCurvatureLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralApproximationJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceClosedLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureTime
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SecondJetBound
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2RelabelingLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory AddCircle
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M63

open M62 SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L S R m0 V0 : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "StateV" => State ((ℤ × Fin 2) × ι)
local notation "Y" => C(AddCircle curvePeriod, W)

theorem exists_closed_normalCurvature_limit_of_spectral_family
    [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hS : 0 < S) (hSone : S ≤ 1) (hSb : a + S < b)
    (hR : 0 ≤ R) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (Vn : ℕ → C(Icc (0 : ℝ) S, StateV)) (V : C(Icc (0 : ℝ) S, StateV))
    (D : ℕ → C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)))
    (d : C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)))
    (psi : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℝ → M) (v0 : ℕ → ℝ)
    (hV : Tendsto Vn atTop (𝓝 V)) (hD : Tendsto D atTop (𝓝 d))
    (hphase : ∀ j (t : Icc (0 : ℝ) S), DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    let D0 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
    let D1 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
    let qn := fun j (t : Icc (0 : ℝ) S) (x : ℝ) => D0 (Vn j t) (x : AddCircle L)
    let pn := fun j (t : Icc (0 : ℝ) S) (x : ℝ) => D1 (Vn j t) (x : AddCircle L)
    let q := fun (t : Icc (0 : ℝ) S) (x : ℝ) => D0 (V t) (x : AddCircle L)
    let p := fun (t : Icc (0 : ℝ) S) (x : ℝ) => D1 (V t) (x : AddCircle L)
    let t0 : Icc (0 : ℝ) S := ⟨0, le_rfl, hS.le⟩
    let f := q t0
    (∀ j t x, qn j t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (pn j t x) ≠ 0) →
    (∀ j t x, qn j t x = e (ρ (qn j t x))) →
    (∀ t x, q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (p t x) ≠ 0) →
    ContDiff ℝ 2 f →
    (∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
      ‖deriv (deriv (qn j t0)) x - deriv (deriv f) x‖ < eps) →
    ∀ ell : ℝ, 0 < ell →
    (∀ j (t : Icc (0 : ℝ) S), ContDiff ℝ 1 (psi j t)) →
    (∀ j (t : Icc (0 : ℝ) S) x, ell ≤ deriv (psi j t) x) →
    (∀ j (t : Icc (0 : ℝ) S) (x : ℝ), D j t (x : AddCircle L) = psi j t x - x) →
    (∀ j x, psi j 0 x = x) →
    (∀ j, M62ShrinkingCurve F (c j)) →
    (∀ j, v0 j ∈ Icc m0 V0) →
    (∀ j x, curveSpeed F (c j) a x = v0 j) →
    (∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R) →
    (∀ j (t : Icc (0 : ℝ) S) x,
      c j x (a + t) = ρ (qn j t (psi j t ((L / curvePeriod) * x)))) →
    ∃ (Hn : ℕ → ℝ → Y) (h : ℝ → Y) (h0 : Y),
      (∀ j, ContinuousOn (Hn j) (Icc a (a + S))) ∧
      (∀ j t, t ∈ Icc a (a + S) → ∀ x : ℝ, Hn j t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x)) ∧
      (∀ x : ℝ, h0 (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f ((L / curvePeriod) * x)))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f ((L / curvePeriod) * y))) a x)) ∧
      Tendsto (fun j => Hn j a) atTop (𝓝 h0) ∧
      ContinuousOn h (Icc a (a + S)) ∧ h a = h0 ∧
      TendstoUniformlyOn Hn h atTop (Icc a (a + S)) ∧
      ∀ eps > 0, ∃ r > 0, ∀ t ∈ Icc a (a + S), t - a < r → ‖h t - h0‖ < eps := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  intro hguard hfixed hguard0 hf hsecond ell hell hpsi hderiv hDrep hpsi0 hc hv0
    hinitial hcurv hslice
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let D0 : StateV →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
  let D1 : StateV →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
  let D2 := vectorPeriodicSecondDerivativeLp (L := L) (ι := ι)
  let Q := fun j t => D0 (Vn j t)
  let P := fun j t => D1 (Vn j t)
  let q := fun t => D0 (V t)
  let p := fun t => D1 (V t)
  let qn := fun j t (x : ℝ) => Q j t (x : AddCircle L)
  let t0 : Icc (0 : ℝ) S := ⟨0, le_rfl, hS.le⟩
  let f : ℝ → W := fun x => q t0 (x : AddCircle L)
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos (Fact.out : 0 < L) (Fact.out : 0 < curvePeriod)
  have haS : a < a + S := lt_add_of_pos_right a hS
  have hab : a < b := haS.trans hSb
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hsub : Icc a (a + S) ⊆ Icc a b := Icc_subset_Icc le_rfl hSb.le
  have hinside {t : ℝ} (ht : t ∈ Ioc a (a + S)) : t ∈ Ioo a b :=
    ⟨ht.1, ht.2.trans_lt hSb⟩
  obtain ⟨hfirst0, rr, hrr, hjets⟩ := exists_spectral_approximation_jets Vn V hV hphase
  change ∀ t (x : ℝ), HasDerivAt (fun y : ℝ => q t (y : AddCircle L))
    (p t (x : AddCircle L)) x at hfirst0
  have hfirst (j : ℕ) (t : Icc (0 : ℝ) S) :
      deriv (qn j t) = fun x : ℝ => P j t (x : AddCircle L) :=
    funext fun x => (hrr j t).2.1 x |>.deriv
  have hfirstf : deriv f = fun x : ℝ => p t0 (x : AddCircle L) :=
    funext fun x => (hfirst0 t0 x).deriv
  have hperiod (g : C(AddCircle L, W)) : Function.Periodic
      (fun x : ℝ => g (x : AddCircle L)) L := by
    intro x
    change g ((x + L : ℝ) : AddCircle L) = g (x : AddCircle L)
    rw [AddCircle.coe_add_period]
  have hdata (j : ℕ) : ∃ H : ℝ → Y, ContinuousOn H (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ x : ℝ, H t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x) := by
    obtain ⟨H, _H1, _H2, _Hd, hH, _, _, _, hrep, _⟩ :=
      exists_periodic_embeddedCurvature_restart_data F (c j) hab (hc j) he
    exact ⟨H, hH, hrep⟩
  choose H hcont hrep using hdata
  have hpush_eq (j : ℕ) (t : ℝ) (g : ℝ → M)
      (hg : (fun y => c j y t) = g) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (g x)
          (m62CurvatureVector F (fun y (_ : ℝ) => g y) t x) :=
    congrArg (fun k : ℝ → M => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (k x)
      (m62CurvatureVector F (fun y (_ : ℝ) => k y) t x) : W)) hg
  have hinitconv : ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
      ‖qn j t0 x - f x‖ < eps ∧ ‖deriv (qn j t0) x - deriv f x‖ < eps ∧
        ‖deriv (deriv (qn j t0)) x - deriv (deriv f) x‖ < eps := by
    intro eps heps
    obtain ⟨N1, hN1⟩ := hjets eps heps
    obtain ⟨N2, hN2⟩ := hsecond eps heps
    refine ⟨max N1 N2, ?_⟩
    intro j hj x
    have hlow := hN1 j ((le_max_left _ _).trans hj) t0
    refine ⟨?_, ?_, hN2 j ((le_max_right _ _).trans hj) x⟩
    · exact ((Q j t0 - q t0).norm_coe_le_norm (x : AddCircle L)).trans_lt hlow.1
    · rw [hfirst, hfirstf]
      exact ((P j t0 - p t0).norm_coe_le_norm (x : AddCircle L)).trans_lt hlow.2.1
  obtain ⟨Hinit, h0, hHinit, hHinitrep, hh0⟩ :=
    exists_uniform_initial_embeddedCurvature_limit F ha he hU heU hρ hρe hf
      (hperiod (q t0)) (fun j => qn j t0) (fun j => (hrr j t0).1)
      (fun j => hperiod (Q j t0))
      (by intro x; rw [hfirstf]; exact hguard0 t0 x)
      (by intro j x; rw [hfirst]; exact hguard j t0 x)
      (fun j x => hfixed j t0 x) hinitconv
  have hstart : Tendsto (fun j => H j a) atTop (𝓝 h0) := by
    have heq (j : ℕ) : H j a = Hinit j := by
      apply ContinuousMap.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      rw [hrep j a ha, hHinitrep]
      apply hpush_eq
      funext y
      have hs := hslice j t0 y
      simpa only [t0, add_zero, hpsi0] using hs
    rw [show (fun j => H j a) = Hinit from funext heq]
    exact hHinit
  obtain ⟨K, hK, hBounds, _hRm, _hRic⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  obtain ⟨C1, hC1, hfirstBound⟩ := m63Exists_boundedCurvature_firstJet_bound F hcompact hR
  let J := Real.sqrt C1
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hjet (j : ℕ) (t : ℝ) (ht : t ∈ Ioc a (a + S)) (x : ℝ) :
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x) ≤
        J / Real.sqrt (t - a) := by
    have hb := hfirstBound (c j) (hc j) (hcurv j) x t (hinside ht)
      (by linarith only [ht.2, hSone])
    have hs := Real.sqrt_le_sqrt hb
    rw [Real.sqrt_div hC1] at hs
    exact hs
  have hcurvnorm (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      m62Curvature F (c j) t x ≤ Real.sqrt R := Real.sqrt_le_sqrt (hcurv j t ht x)
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let Vcap := V0 * Real.exp ((K + R) * S)
  have hVcap : 0 ≤ Vcap := mul_nonneg (hm0.le.trans hmV) (Real.exp_pos _).le
  have hspeed (j : ℕ) (t : ℝ) (ht : t ∈ Ioc a (a + S)) (x : ℝ) :
      curveSpeed F (c j) t x ≤ Vcap := by
    have hv := (curveSpeed_exp_bounds F (c j) (hc j) hBounds x
      (fun r hr => hcurv j r hr x) ha (hsub ⟨ht.1.le, ht.2⟩) ht.1.le).2
    rw [hinitial j x] at hv
    apply hv.trans
    exact mul_le_mul (hv0 j).2
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by linarith only [ht.2]) (add_nonneg hK hR)))
      (Real.exp_pos _).le (hm0.le.trans hmV)
  have hLip (t : ℝ) (ht : t ∈ Ioc a (a + S)) :
      ∃ C : ℝ≥0, ∀ j, LipschitzWith C (fun x : ℝ => H j t (x : AddCircle curvePeriod)) := by
    let C := Vcap * (E1 * (J / Real.sqrt (t - a)) + E2 * Real.sqrt R)
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨⟨C, hC⟩, ?_⟩
    intro j
    have heq : (fun x : ℝ => H j t (x : AddCircle curvePeriod)) =
        fun x => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t)
          (m62CurvatureVector F (c j) t x) : W) :=
      funext (hrep j t (hsub ⟨ht.1.le, ht.2⟩))
    rw [heq]
    apply lipschitzWith_of_nnnorm_deriv_le
    · intro x
      exact (hasDerivAt_embeddedCurvature_spatial F (c j) (hc j) he (hinside ht) x).differentiableAt
    · intro x
      have hd := (embeddedCurvature_derivative_remainder_bounds F (c j) (hc j) he
        hK hK hK hBounds (hinside ht) x hE1 hE2 hE3
        (fun A => (hE t (hsub ⟨ht.1.le, ht.2⟩) (c j x t) A 0 0).1)
        (fun A B => (hE t (hsub ⟨ht.1.le, ht.2⟩) (c j x t) A B 0).2.1)
        (fun A B C => (hE t (hsub ⟨ht.1.le, ht.2⟩) (c j x t) A B C).2.2)).1
      change ‖deriv (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j y t)
        (m62CurvatureVector F (c j) t y) : W)) x‖ ≤ C
      apply hd.trans
      exact mul_le_mul (hspeed j t ht x)
        (add_le_add (mul_le_mul_of_nonneg_left (hjet j t ht x) hE1)
          (mul_le_mul_of_nonneg_left (hcurvnorm j t (hinside ht) x) hE2))
        (add_nonneg (mul_nonneg hE1 (Real.sqrt_nonneg _))
          (mul_nonneg hE2 (curvature_nonneg F (c j) t x))) hVcap
  let scaleH := AddCircle.homeomorphAddCircle curvePeriod L
    (Fact.out : 0 < curvePeriod).ne' (Fact.out : 0 < L).ne'
  let scale : C(AddCircle curvePeriod, AddCircle L) := ⟨scaleH, scaleH.continuous⟩
  let unscale : C(AddCircle L, AddCircle curvePeriod) := ⟨scaleH.symm, scaleH.symm.continuous⟩
  have hunscale (x : ℝ) : unscale (x : AddCircle L) = ((x / κ : ℝ) : AddCircle curvePeriod) := by
    change ((x * (L⁻¹ * curvePeriod) : ℝ) : AddCircle curvePeriod) = _
    congr 1
    dsimp only [κ]
    field_simp
  have hL2 (t : ℝ) (ht : t ∈ Ioc a (a + S)) :
      CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (H j t)) := by
    let u : Icc (0 : ℝ) S := ⟨t - a, by constructor <;> linarith only [ht.1, ht.2]⟩
    have htime : a + (u : ℝ) = t := by dsimp only [u]; ring
    have hQ := (D0.continuous.tendsto (V u)).comp
      (((continuous_eval_const u).tendsto V).comp hV)
    have hP := (D1.continuous.tendsto (V u)).comp
      (((continuous_eval_const u).tendsto V).comp hV)
    have hr : CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (rr j u)) := by
      have hd2 := (D2.continuous.tendsto (V u)).comp
        (((continuous_eval_const u).tendsto V).comp hV)
      have heq (j : ℕ) : D2 (Vn j u) = ContinuousMap.toLp 2 haarAddCircle ℝ (rr j u) :=
        (hrr j u).2.2.2.2
      simpa only [Function.comp_def, heq] using hd2.cauchySeq
    obtain ⟨G, _w, hGrep, _hwrep, hGL2, _hwL2⟩ :=
      exists_cauchySeq_ambientCurvature_labelVelocity_L2 F he hU heU hρ hρe
        (hsub ⟨ht.1.le, ht.2⟩) (fun j => Q j u) (fun j => P j u) (fun j => rr j u)
        (q u) (p u) (fun j => (hrr j u).2.1) (fun j => (hrr j u).2.2.1)
        (by intro j z; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z; exact hguard j u x)
        (by intro j z; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z; exact hfixed j u x)
        (by intro z; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z; exact hguard0 u x)
        hQ hP hr
    have hnormal (j : ℕ) (x : ℝ) :
        H j t (x : AddCircle curvePeriod) = G j ((psi j u (κ * x) : ℝ) : AddCircle L) := by
      let gamma := fun y (_ : ℝ) => ρ (qn j u y)
      let phi := fun y => psi j u (κ * y)
      have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => gamma y t) :=
        (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
          (hrr j u).1.contMDiff (fun y => (hguard j u y).1)
      have hvel (y : ℝ) : curveVelocity (n := n) (fun z => gamma z t) y =
          mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j u y) (P j u (y : AddCircle L)) := by
        change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ qn j u) y 1 = _
        erw [mfderiv_comp y
          ((hρ.contMDiffAt (hU.mem_nhds (hguard j u y).1)).mdifferentiableAt (by simp))
          ((hrr j u).2.1 y).differentiableAt.mdifferentiableAt,
          ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv,
          ((hrr j u).2.1 y).hasFDerivAt.fderiv]
        exact congrArg (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j u y))
          (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (P j u (y : AddCircle L)))
      have himm (y : ℝ) : curveVelocity (n := n) (fun z => gamma z t) y ≠ 0 := by
        rw [hvel]
        exact (hguard j u y).2
      have hunit := unitTangent_contMDiff_of_c2 F gamma (t := t) hgamma himm
      have hphi (y : ℝ) : HasDerivAt phi (deriv (psi j u) (κ * y) * κ) y := by
        have hlin : HasDerivAt (fun z : ℝ => κ * z) κ y := by
          simpa +instances only [id_eq, mul_one] using! (hasDerivAt_id y).const_mul κ
        simpa only [phi, Function.comp_def, smul_eq_mul, mul_comm] using
          ((hpsi j u).differentiable (by norm_num) (κ * y)).hasDerivAt.scomp y hlin
      have hphiPos (y : ℝ) : 0 < deriv phi y := by
        rw [(hphi y).deriv]
        exact mul_pos (hell.trans_le (hderiv j u _)) hκ
      have hcurve : (fun y => c j y t) = fun y => gamma (phi y) t := by
        funext y
        have hs := hslice j u y
        rwa [htime] at hs
      rw [hrep j t (hsub ⟨ht.1.le, ht.2⟩), hpush_eq j t _ hcurve]
      change mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma (phi x) t)
        (m62CurvatureVector F (fun y s => gamma (phi y) s) t x) = _
      rw [curvatureVector_comp F gamma (hgamma.mdifferentiable (by norm_num))
        (fun y => (hphi y).differentiableAt) hphiPos
        ((hunit (phi x)).mdifferentiableAt (by norm_num))]
      exact (hGrep j (phi x)).symm
    let Hphys (j : ℕ) : C(AddCircle L, W) := (H j t).comp unscale
    have hcomp (j : ℕ) (x : ℝ) : Hphys j (x : AddCircle L) = G j (psi j u x : AddCircle L) := by
      change H j t (unscale (x : AddCircle L)) = _
      rw [hunscale, hnormal]
      congr 2
      field_simp
    have hshift (j : ℕ) (x : ℝ) : psi j u (x + L) = psi j u x + L := by
      have heq : D j u ((x + L : ℝ) : AddCircle L) = D j u (x : AddCircle L) := by
        rw [AddCircle.coe_add_period]
      rw [hDrep, hDrep] at heq
      linarith
    have hlabels : ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ m ≥ N,
        ∀ x ∈ Icc 0 L, |psi j u x - psi m u x| < eps := by
      intro eps heps
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hD.cauchySeq eps heps
      refine ⟨N, ?_⟩
      intro j hj m hm x _hx
      have htimeNorm := (D j - D m).norm_coe_le_norm u
      have hxNorm := (D j u - D m u).norm_coe_le_norm (x : AddCircle L)
      have hnorm : ‖D j - D m‖ < eps :=
        (_root_.dist_eq_norm (D j) (D m)).symm.trans_lt (hN j hj m hm)
      have htot := hxNorm.trans_lt (htimeNorm.trans_lt hnorm)
      change ‖D j u (x : AddCircle L) - D m u (x : AddCircle L)‖ < eps at htot
      rw [hDrep, hDrep, sub_sub_sub_cancel_right, Real.norm_eq_abs] at htot
      exact htot
    obtain ⟨C, hC⟩ := hLip t ht
    have hLipphys (j : ℕ) : LipschitzWith ⟨(C : ℝ) / κ, div_nonneg C.coe_nonneg hκ.le⟩
        (fun x : ℝ => Hphys j (x : AddCircle L)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (H j t (unscale (x : AddCircle L)))
        (H j t (unscale (y : AddCircle L))) ≤ ((C : ℝ) / κ) * dist x y
      rw [hunscale, hunscale]
      have hb := (hC j).dist_le_mul (x / κ) (y / κ)
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hκ] at hb
      exact hb.trans_eq (by rw [Real.dist_eq]; ring)
    have hCauchy := cauchySeq_periodic_comp_of_cauchySeq_L2 G Hphys
      (fun j => psi j u) hell (fun j => hpsi j u) hshift
      (fun j => hderiv j u) hlabels hGL2 hcomp hLipphys
    obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hback := (scale.continuous_precomp.tendsto g).comp hg
    have hbackeq (j : ℕ) : (Hphys j).comp scale = H j t := by
      apply ContinuousMap.ext
      intro z
      exact congrArg (H j t) (scaleH.symm_apply_apply z)
    simp only [Function.comp_def, hbackeq] at hback
    exact (((ContinuousMap.toLp 2 haarAddCircle ℝ).continuous.tendsto _).comp hback).cauchySeq
  have hequi : ∀ d0 ∈ Ioc a (a + S), ∀ eps > 0, ∃ eta > 0, ∀ j s,
      s ∈ Icc d0 (a + S) → ∀ t ∈ Icc d0 (a + S),
        |t - s| < eta → ‖H j t - H j s‖ < eps := by
    intro d0 hd0 eps heps
    have hdelta : 0 < d0 - a := sub_pos.mpr hd0.1
    obtain ⟨C2, hC2, hsecondBound⟩ :=
      m63SecondJetSquared_bound_of_curvature_bound F hcompact hR hdelta
    let J1 := J / Real.sqrt (d0 - a)
    let J2 := Real.sqrt C2
    have hJ1 : 0 ≤ J1 := div_nonneg hJ (Real.sqrt_nonneg _)
    have hJ2 : 0 ≤ J2 := Real.sqrt_nonneg _
    obtain ⟨Ct, hCt, htime⟩ := exists_uniform_embeddedCurvature_time_lipschitz
      F hcompact hab he hK hK hK hBounds (Real.sqrt_nonneg R) hJ1 hJ2
    have htimebound (j : ℕ) (s : ℝ) (hs : s ∈ Icc d0 (a + S))
        (t : ℝ) (ht : t ∈ Icc d0 (a + S)) : ‖H j t - H j s‖ ≤ Ct * |t - s| := by
      apply (ContinuousMap.norm_le _ (mul_nonneg hCt (abs_nonneg _))).mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      change ‖H j t (x : AddCircle curvePeriod) - H j s (x : AddCircle curvePeriod)‖ ≤ _
      rw [hrep j t (hsub ⟨hd0.1.le.trans ht.1, ht.2⟩),
        hrep j s (hsub ⟨hd0.1.le.trans hs.1, hs.2⟩)]
      apply htime (c j) (hc j) d0 (a + S) hd0.1.le hd0.2 hSb.le
        (fun r hr y => hcurvnorm j r ⟨hd0.1.trans hr.1, hr.2.trans hSb⟩ y)
        (fun r hr y => (hjet j r ⟨hd0.1.trans hr.1, hr.2.le⟩ y).trans
          (div_le_div_of_nonneg_left hJ (Real.sqrt_pos.mpr hdelta)
            (Real.sqrt_le_sqrt (sub_le_sub_right hr.1.le a))))
        (fun r hr y => ?_) t ht s hs x
      exact Real.sqrt_le_sqrt (hsecondBound (c j) (hc j) (hcurv j) y r
        ⟨hd0.1.trans hr.1, hr.2.trans hSb⟩ (sub_le_sub_right hr.1.le a))
    refine ⟨eps / (Ct + 1), by positivity, ?_⟩
    intro j s hs t ht hdist
    apply (htimebound j s hs t ht).trans_lt
    calc
      Ct * |t - s| ≤ (Ct + 1) * |t - s| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (Ct + 1) * (eps / (Ct + 1)) :=
        mul_lt_mul_of_pos_left hdist (by positivity)
      _ = eps := by field_simp
  let F' := m63RestrictClosedFlow F a (a + S) hsub haS
  have hc' (j : ℕ) : M62ShrinkingCurve F' (c j) :=
    m63SmoothRestriction (m63SmoothClosed_iff_m62.mpr (hc j)) a (a + S) hsub haS
  have hjetEq (j i : ℕ) (t x : ℝ) : m63CurvatureJet F' (c j) i t x =
      m63CurvatureJet F (c j) i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F (c j) t (fun y => m63CurvatureJet F' (c j) i t y) x =
        m62SpatialDerivative F (c j) t (fun y => m63CurvatureJet F (c j) i t y) x
      rw [show (fun y => m63CurvatureJet F' (c j) i t y) =
        (fun y => m63CurvatureJet F (c j) i t y) from funext ih]
  obtain ⟨h, hh, hha, hlim, htrace⟩ := exists_closed_uniform_embeddedCurvature_limit
    F' haS hcompact he hK hR hJ (m63RestrictAmbientBounds hBounds a (a + S) hsub haS)
    hm0 hmV c hc' v0 hv0 hinitial
    (fun j t ht x => hcurv j t (hinside ⟨ht.1, ht.2.le⟩) x)
    (by
      intro j t ht x
      change (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F' (c j) 1 t x) ≤ _
      rw [hjetEq]
      exact hjet j t ⟨ht.1, ht.2.le⟩ x)
    H h0 (fun j t ht => hrep j t (hsub ht)) hstart hL2 hequi
  exact ⟨H, h, h0, fun j => (hcont j).mono hsub,
    fun j t ht => hrep j t (hsub ht), hh0, hstart, hh, hha, hlim, htrace⟩

end PoincareConjecture.M63
