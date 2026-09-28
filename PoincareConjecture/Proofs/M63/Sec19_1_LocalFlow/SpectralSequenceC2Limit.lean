import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonNormalFieldExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.NormalFieldC2Reconstruction
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedSpeedGradientPath
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedJetLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L δ R J : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "StateV" => State ((ℤ × Fin 2) × ι)
local notation "X" => C(AddCircle L, W)
local notation "Y" => C(AddCircle curvePeriod, W)
local notation "YR" => C(AddCircle curvePeriod, ℝ)




theorem exists_spectral_sequence_c2_threeJet_limit
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hδ : 0 < δ) (hδone : 2 * δ ≤ 1) (hδb : a + 2 * δ < b)
    (hR : 0 ≤ R) (hJ : 0 ≤ J)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (Vn : ℕ → C(Icc (0 : ℝ) δ, StateV))
    (V : C(Icc (0 : ℝ) δ, StateV))
    (hV : Tendsto Vn atTop (𝓝 V))
    (qn : ℕ → ℝ → ℝ → W)
    (hq : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (qn j)) (Icc 0 δ ×ˢ univ))
    (hphase : ∀ j (t : Icc (0 : ℝ) δ), DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0)
    (psi : ℕ → ℝ → ℝ → ℝ)
    (hpsi : ∀ j, ContDiffOn ℝ 1 (Function.uncurry (psi j)) (Icc 0 δ ×ˢ univ))
    (hshift : ∀ j t, t ∈ Icc 0 δ → ∀ x,
      psi j t (x + L) = psi j t x + L)
    (hpsi0 : ∀ j x, psi j 0 x = x)
    (hpsipos : ∀ j t, t ∈ Icc 0 δ → ∀ x, 0 < deriv (psi j t) x)
    (hode : ∀ j t, t ∈ Ioo 0 δ → ∀ x,
      HasDerivAt (fun r => psi j r x)
        (deriv (fun y => ambientCurvePrincipal F ρ (a + t)
          (qn j t y) (deriv (qn j t) y)) (psi j t x) / 2) t)
    (m : ℕ → ℝ) (mstar : ℝ)
    (hm : ∀ j, m j ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (_hmstar : mstar ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (hmlim : Tendsto m atTop (𝓝 mstar))
    (hspeed : ∀ j x, curveSpeed F (fun y _ => ρ (qn j 0 y)) a x = m j)
    (f : X) (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L)))
    (hinit : ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x : ℝ,
      ‖qn j 0 x - f (x : AddCircle L)‖ < eps ∧
      ‖deriv (qn j 0) x - deriv (fun y : ℝ => f (y : AddCircle L)) x‖ < eps ∧
      ‖deriv (deriv (qn j 0)) x -
        deriv (deriv (fun y : ℝ => f (y : AddCircle L))) x‖ < eps) :
    let κ := L / curvePeriod
    let jet := fun (z : StateV) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
    let cn := fun j x t => ρ (qn j (t - a) (psi j (t - a) (κ * x)))
    (∀ j (t : Icc (0 : ℝ) δ) (x : ℝ),
      jet (Vn j t) (x : AddCircle L) = (qn j t x, deriv (qn j t) x)) →
    (∀ j (t : Icc (0 : ℝ) δ) x, qn j t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (deriv (qn j t) x) ≠ 0) →
    (∀ j (t : Icc (0 : ℝ) δ) x, qn j t x = e (ρ (qn j t x))) →
    (∀ (t : Icc (0 : ℝ) δ) (x : AddCircle L),
      (jet (V t) x).1 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet (V t) x).1 (jet (V t) x).2 ≠ 0) →
    (∀ x : ℝ, (jet (V ⟨0, le_rfl, hδ.le⟩) (x : AddCircle L)).1 =
      f (x : AddCircle L)) →
    (∀ j, M63SmoothShrinkingCurveOn F (cn j) (Icc a (a + 2 * δ))) →
    (∀ j t, t ∈ Icc a (a + 2 * δ) → ∀ x,
      m62CurvatureSquared F (cn j) t x ≤ R) →
    (∀ j t, t ∈ Ioo a (a + 2 * δ) → ∀ x,
      (F.metric t).tangentNorm (cn j x t) (m63CurvatureJet F (cn j) 1 t x) ≤
        J / Real.sqrt (t - a)) →
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ c0 : ℝ → ℝ → M,
        M63C2ShrinkingCurveOn F c0 (Icc a (a + δ)) ∧
        (∀ x, c0 x a = ρ (f ((κ * x : ℝ) : AddCircle L))) ∧
        (∀ x, curveSpeed F c0 a x = κ * mstar) ∧
        ∃ (Q0 Q1 Q2 : ℕ → C(Icc a (a + δ), Y))
          (q0 q1 q2 : C(Icc a (a + δ), Y)),
          Tendsto Q0 atTop (𝓝 q0) ∧ Tendsto Q1 atTop (𝓝 q1) ∧
          Tendsto Q2 atTop (𝓝 q2) ∧
          (∀ j (t : Icc a (a + δ)) (x : ℝ),
            Q0 j t (x : AddCircle curvePeriod) = e (cn (sigma j) x t) ∧
            Q1 j t (x : AddCircle curvePeriod) =
              deriv (fun y => e (cn (sigma j) y t)) x ∧
            Q2 j t (x : AddCircle curvePeriod) =
              deriv (deriv (fun y => e (cn (sigma j) y t))) x) ∧
          (∀ (t : Icc a (a + δ)) (x : ℝ),
            q0 t (x : AddCircle curvePeriod) = e (c0 x t) ∧
            q1 t (x : AddCircle curvePeriod) = deriv (fun y => e (c0 y t)) x ∧
            q2 t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (c0 y t))) x) ∧
          ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ (t : Icc a (a + δ)) (x : ℝ),
            ‖e (cn (sigma j) x t) - e (c0 x t)‖ < eps ∧
            ‖deriv (fun y => e (cn (sigma j) y t)) x -
              deriv (fun y => e (c0 y t)) x‖ < eps ∧
            ‖deriv (deriv (fun y => e (cn (sigma j) y t))) x -
              deriv (deriv (fun y => e (c0 y t))) x‖ < eps := by
  classical
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  dsimp only
  intro hdecode hguard hfixed hguard0 hzero hcn hcap hjet
  let κ := L / curvePeriod
  let jet : StateV → AddCircle L → W × W := fun z x =>
    (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  let cn := fun j x t => ρ (qn j (t - a) (psi j (t - a) (κ * x)))
  have hdecodeJet (j : ℕ) (t : Icc (0 : ℝ) δ) (x : ℝ) :
      jet (Vn j t) (x : AddCircle L) = (qn j t x, deriv (qn j t) x) := hdecode j t x
  have hκ : 0 < κ := div_pos Fact.out Real.two_pi_pos
  have haδ : a < a + δ := lt_add_of_pos_right a hδ
  have ha2δ : a < a + 2 * δ := by linarith only [hδ]
  have hδwide : a + δ < a + 2 * δ := by linarith only [hδ]
  have hwideF : Icc a (a + 2 * δ) ⊆ Icc a b := Icc_subset_Icc_right hδb.le
  have hshortwide : Icc a (a + δ) ⊆ Icc a (a + 2 * δ) :=
    Icc_subset_Icc_right hδwide.le
  have hshortF : Icc a (a + δ) ⊆ Icc a b := hshortwide.trans hwideF
  let Fwide := m63RestrictClosedFlow F a (a + 2 * δ) hwideF ha2δ
  let Fshort := m63RestrictClosedFlow F a (a + δ) hshortF haδ
  have hcnwide (j : ℕ) : M62ShrinkingCurve Fwide (cn j) :=
    m63SmoothRestriction (hcn j) a (a + 2 * δ) Subset.rfl ha2δ
  have hcnshort (j : ℕ) : M62ShrinkingCurve Fshort (cn j) :=
    m63SmoothRestriction (hcn j) a (a + δ) hshortwide haδ
  obtain ⟨Kambient, hKambient, hBounds, _hRm, _hRic⟩ :=
    m63Exists_firstJet_ambient_bounds F hcompact
  have hBoundsShort : CurveEvolutionAmbientBounds Fshort Kambient Kambient Kambient :=
    m63RestrictAmbientBounds hBounds a (a + δ) hshortF haδ
  have hBoundsWide : CurveEvolutionAmbientBounds Fwide Kambient Kambient Kambient :=
    m63RestrictAmbientBounds hBounds a (a + 2 * δ) hwideF ha2δ
  have hT0 : (0 : ℝ) ∈ Icc 0 δ := ⟨le_rfl, hδ.le⟩
  have hqslice (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 δ) : ContDiff ℝ ∞ (qn j t) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ => (t, x)) := contDiff_const.prodMk contDiff_id
    exact (hq j).comp_contDiff hmap (fun _ => ⟨ht, mem_univ _⟩)
  have hpsislice (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 δ) : ContDiff ℝ 1 (psi j t) := by
    have hmap : ContDiff ℝ 1 (fun x : ℝ => (t, x)) := contDiff_const.prodMk contDiff_id
    exact (hpsi j).comp_contDiff hmap (fun _ => ⟨ht, mem_univ _⟩)
  have hnguard (j : ℕ) (t : Icc (0 : ℝ) δ) (x : AddCircle L) :
      (jet (Vn j t) x).1 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet (Vn j t) x).1 (jet (Vn j t) x).2 ≠ 0 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    erw [hdecodeJet]
    exact hguard j t y
  obtain ⟨K, hK, hKU, _hK0, hKn, mu, Lambda, hmu, hLambda,
      _LA, _LB, _LD, hprincipal, _hAlip, _hBlip, _hDlip⟩ :=
    exists_compact_spectral_family_jet_domain F he hU hρ Vn V hV hnguard hguard0
  have hqmem (j : ℕ) (t : Icc (0 : ℝ) δ) (x : ℝ) :
      (qn j t x, deriv (qn j t) x) ∈ K := by
    have hx := hKn j t (x : AddCircle L)
    change jet (Vn j t) (x : AddCircle L) ∈ K at hx
    rwa [hdecodeJet] at hx
  have hspatial (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 δ) :
      MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun x => ρ (qn j t x)) := by
    intro x
    exact ((hρ.contMDiffAt (hU.mem_nhds (hguard j ⟨t, ht⟩ x).1)).mdifferentiableAt
      (by simp)).comp x ((hqslice j t ht).contMDiff.mdifferentiable (by simp) x)
  have hvelocity (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 δ) (x : ℝ) :
      curveVelocity (n := n) (fun y => ρ (qn j t y)) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (deriv (qn j t) x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ qn j t) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hguard j ⟨t, ht⟩ x).1)).mdifferentiableAt (by simp))
      ((hqslice j t ht).contMDiff.mdifferentiable (by simp) x),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have hcn0 (j : ℕ) (x : ℝ) : cn j x a = ρ (qn j 0 (κ * x)) := by
    change ρ (qn j (a - a) (psi j (a - a) (κ * x))) = _
    rw [sub_self, hpsi0]
  have hinitspeed (j : ℕ) (x : ℝ) : curveSpeed F (cn j) a x = κ * m j := by
    calc
      _ = curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 (κ * y))) a x :=
        curveSpeed_congr_slice F (hcn0 j)
      _ = κ * curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 y)) a (κ * x) :=
        curveSpeed_comp F (fun y (_ : ℝ) => ρ (qn j 0 y)) (t := a) (x := x)
          (hspatial j 0 hT0 _) (by
          simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul κ) hκ.le
      _ = κ * m j := congrArg (κ * ·) (hspeed j _)
  have hshiftmem (t : ℝ) (ht : t ∈ Icc a (a + δ)) : t - a ∈ Icc (0 : ℝ) δ :=
    ⟨sub_nonneg.mpr ht.1, by linarith only [ht.2]⟩
  let ell := (1 / 2 : ℝ) * Real.exp (-(Kambient + R) * ((a + δ) - a)) * Real.sqrt mu
  let upper := (3 / 2 : ℝ) * Real.exp ((Kambient + R) * ((a + δ) - a)) * Real.sqrt Lambda
  have hlabelbounds (j : ℕ) : 0 < ell ∧ 0 < upper ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ x, ell ≤ deriv (psi j t) x ∧ deriv (psi j t) x ≤ upper := by
    have hb := normalLabel_derivative_bounds Fshort haδ
      (fun x t => ρ (qn j (t - a) x)) (fun t => psi j (t - a))
      hκ (hm j).1 (hm j).2 hmu hLambda hKambient hR hBoundsShort
      (fun t ht => hspatial j (t - a) (hshiftmem t ht))
      (fun t ht x => by
        rw [hvelocity j (t - a) (hshiftmem t ht)]
        exact (hguard j ⟨t - a, hshiftmem t ht⟩ x).2)
      (fun t ht => (hpsislice j (t - a) (hshiftmem t ht)).differentiable (by norm_num))
      (fun t ht => hpsipos j (t - a) (hshiftmem t ht))
      (fun x => by simpa only [sub_self] using hpsi0 j x)
      (fun x => by
        change curveSpeed F (fun y t => ρ (qn j (t - a) y)) a x = m j
        calc
          _ = curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 y)) a x :=
            curveSpeed_congr_slice F (fun y => by rw [sub_self])
          _ = m j := hspeed j x)
      (fun t ht x => by
        have hp := hprincipal t (hshortF ht) _ (hqmem j ⟨t - a, hshiftmem t ht⟩ x)
        have heq : ambientCurvePrincipal F ρ t (qn j (t - a) x)
            (deriv (qn j (t - a)) x) =
              (curveSpeed Fshort (fun y s => ρ (qn j (s - a) y)) t x ^ 2)⁻¹ := by
          unfold ambientCurvePrincipal
          rw [← hvelocity j (t - a) (hshiftmem t ht)]
          exact congrArg (fun z : ℝ => z⁻¹) (M62.speed_sq Fshort
            (fun y s => ρ (qn j (s - a) y)) t x).symm
        rwa [heq] at hp)
      (hcnshort j) (fun t ht => hcap j t (hshortwide (Ioo_subset_Icc_self ht)))
    refine ⟨hb.1, hb.2.1, ?_⟩
    intro t ht x
    have hat : a + t ∈ Icc a (a + δ) :=
      ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    simpa only [ell, upper, add_sub_cancel_left] using hb.2.2 (a + t) hat x
  have hell : 0 < ell := (hlabelbounds 0).1
  obtain ⟨sigma, Dn, d, hsigma, hVseq, hDlim, hDrep, hd0⟩ :=
    exists_compact_spectral_label_displacements F hU hρ hδ
      (show δ < b - a by linarith only [hδb, hδ]) hK hKU Vn V hV qn hq
      (fun j t x => (congrArg Prod.fst (hdecode j t x)).symm)
      hphase hKn psi hpsi hshift hpsi0 hode hell
      (fun j t ht x => ((hlabelbounds j).2.2 t ht x).1)
      (fun j t ht x => ((hlabelbounds j).2.2 t ht x).2)
  let cseq := fun j => cn (sigma j)
  let vinit := fun j => κ * m (sigma j)
  have hvinit (j : ℕ) : vinit j ∈ Icc (κ / 2) (3 * κ / 2) := by
    have hlo := mul_le_mul_of_nonneg_left (hm (sigma j)).1 hκ.le
    have hhi := mul_le_mul_of_nonneg_left (hm (sigma j)).2 hκ.le
    constructor <;> dsimp only [vinit] <;> linarith only [hlo, hhi]
  have hvlim : Tendsto vinit atTop (𝓝 (κ * mstar)) := by
    simpa only [vinit, Function.comp_def] using
      (tendsto_const_nhds.mul (hmlim.comp hsigma.tendsto_atTop))
  have hm0 : 0 < κ / 2 := half_pos hκ
  have hmV : κ / 2 ≤ 3 * κ / 2 := by linarith only [hκ]
  have hzeroFun : (fun y : ℝ => (jet (V ⟨0, le_rfl, hδ.le⟩)
      (y : AddCircle L)).1) = (fun y : ℝ => f (y : AddCircle L)) := funext hzero
  obtain ⟨Rn, Sn, Hn, r, s, h, hRn, hSn, hHn, hRrep, hSrep, hHrep, hrU, hr0⟩ :=
    exists_closed_normal_geometric_fields_of_spectral_family Fwide hcompact hδ
      (show δ ≤ 1 by linarith only [hδone, hδ]) hδwide
      hR hm0 hmV he hU heU hρ hρe (fun j => Vn (sigma j)) V Dn d
      (fun j => psi (sigma j)) cseq vinit hVseq hDlim (fun j => hphase (sigma j))
      (fun j t x => hnguard (sigma j) t (x : AddCircle L))
      (fun j t x => by
        change (jet (Vn (sigma j) t) (x : AddCircle L)).1 =
          e (ρ ((jet (Vn (sigma j) t) (x : AddCircle L)).1))
        rw [hdecodeJet]
        exact hfixed (sigma j) t x)
      (fun t x => hguard0 t (x : AddCircle L))
      (by
        change ContDiff ℝ 2 (fun y : ℝ =>
          (jet (V ⟨0, le_rfl, hδ.le⟩) (y : AddCircle L)).1)
        rw [hzeroFun]
        exact hf)
      (by
        intro eps heps
        obtain ⟨N, hN⟩ := hinit eps heps
        refine ⟨N, fun j hj x => ?_⟩
        have hn : (fun y : ℝ => (jet (Vn (sigma j) ⟨0, le_rfl, hδ.le⟩)
            (y : AddCircle L)).1) = qn (sigma j) 0 :=
          funext fun y => congrArg Prod.fst (hdecode (sigma j) ⟨0, le_rfl, hδ.le⟩ y)
        change ‖deriv (deriv (fun y : ℝ => (jet (Vn (sigma j) ⟨0, le_rfl, hδ.le⟩)
          (y : AddCircle L)).1)) x - deriv (deriv (fun y : ℝ =>
            (jet (V ⟨0, le_rfl, hδ.le⟩) (y : AddCircle L)).1)) x‖ < eps
        rw [hn, hzeroFun]
        exact (hN (sigma j) (hj.trans (hsigma.id_le j)) x).2.2)
      ell hell (fun j t => hpsislice (sigma j) t t.property)
      (fun j t x => ((hlabelbounds (sigma j)).2.2 t t.property x).1) hDrep
      (fun j => hpsi0 (sigma j)) (fun j => hcnwide (sigma j)) hvinit
      (fun j => hinitspeed (sigma j))
      (fun j t ht => hcap (sigma j) t (Ioo_subset_Icc_self ht))
      (fun j t x => by
        change ρ (qn (sigma j) ((a + t) - a)
          (psi (sigma j) ((a + t) - a) (κ * x))) = _
        rw [add_sub_cancel_left]
        exact congrArg ρ (congrArg Prod.fst
          (hdecode (sigma j) t (psi (sigma j) t (κ * x)))).symm) hd0
  have hcapshort (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a (a + δ)) (x : ℝ) :
      m62CurvatureSquared Fshort (cseq j) t x ≤ R :=
    hcap (sigma j) t (hshortwide (Ioo_subset_Icc_self ht)) x
  have hjetshort (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a (a + δ)) (x : ℝ) :
      (Fshort.metric t).tangentNorm (cseq j x t) (m63CurvatureJet Fshort (cseq j) 1 t x) ≤
        J / Real.sqrt (t - a) :=
    hjet (sigma j) t ⟨ht.1, ht.2.trans hδwide⟩ x
  obtain ⟨Vs, Ws, v, g, hVs, hWs, hvc, hgc, hVslim, hWslim,
      hvbounds, _hv0, _hg0, _hvg⟩ :=
    exists_normal_speed_fields_limits Fshort haδ hcompact he hU heU hρ hρe
      hKambient hR hJ hBoundsShort hm0 hmV cseq (fun j => hcnshort (sigma j))
      vinit (κ * mstar) hvinit hvlim (fun j => hinitspeed (sigma j))
      hcapshort hjetshort Rn Sn Hn r s h hRn hSn hHn hRrep hSrep hHrep hrU
  have hvpos (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      0 < v t (x : AddCircle curvePeriod) :=
    (mul_pos hm0 (Real.exp_pos _)).trans_le (hvbounds t ht x).1
  let c0 : ℝ → ℝ → M := fun x t =>
    ρ (r (projIcc a (a + δ) haδ.le t) (x : AddCircle curvePeriod))
  obtain ⟨hc0short, hfields, hspeed0, _hprimitive⟩ :=
    normalField_c2_reconstruction_with_anchored_speed Fshort haδ
      he hU heU hρ hρe hKambient hR hBoundsShort hm0 hmV
      cseq (fun j => hcnshort (sigma j)) vinit (κ * mstar) hvinit hvlim
      (fun j => hinitspeed (sigma j)) hcapshort Rn Sn Hn r s h hRn hSn hHn
      hRrep hSrep hHrep hrU Vs Ws v g hVs hWs hvc hgc hVslim hWslim hvpos
  have hc0 : M63C2ShrinkingCurveOn F c0 (Icc a (a + δ)) := {
    domain_subset := hshortF
    periodic := hc0short.periodic
    spatial_regular := hc0short.spatial_regular
    joint_c1 := hc0short.joint_c1
    immersed := hc0short.immersed
    continuous := hc0short.continuous
    velocity_continuous := hc0short.velocity_continuous
    curvature_continuous := hc0short.curvature_continuous
    equation := hc0short.equation }
  have hc0initial (x : ℝ) : c0 x a = ρ (f ((κ * x : ℝ) : AddCircle L)) := by
    change ρ (r (projIcc a (a + δ) haδ.le a) (x : AddCircle curvePeriod)) = _
    rw [projIcc_of_mem haδ.le ⟨le_rfl, haδ.le⟩, hr0]
    exact congrArg ρ (hzero (κ * x))
  have hquot : IsOpenQuotientMap
      (fun z : Icc a (a + δ) × ℝ => (z.1, (z.2 : AddCircle curvePeriod))) :=
    IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
  have hVscont (j : ℕ) : ContinuousOn (Vs j) (Icc a (a + δ)) := by
    have hlift : ContinuousOn (fun z : ℝ × ℝ => Vs j z.2 (z.1 : AddCircle curvePeriod))
        (univ ×ˢ Icc a (a + δ)) :=
      (M62.speed_continuousOn Fshort (cseq j) (hcnshort (sigma j))).congr
        (fun z hz => hVs j z.2 hz.2 z.1)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hquot.continuous_comp_iff.mp
      (hlift.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun z => ⟨mem_univ _, z.1.2⟩))
  have hWspath (j : ℕ) : ∃ G : C(Icc a (a + δ), YR),
      ∀ (t : Icc a (a + δ)) (x : ℝ),
        G t (x : AddCircle curvePeriod) = deriv (curveSpeed Fshort (cseq j) t) x := by
    exact exists_closed_curveSpeed_gradient_path Fwide (cseq j) (hcnwide (sigma j))
      hKambient hR hJ (hm0.trans_le (hvinit j).1) hBoundsWide
      (hinitspeed (sigma j))
      (fun t ht => hcap (sigma j) t (Ioo_subset_Icc_self ht))
      (fun t ht => hjet (sigma j) t ht) haδ.le hδwide
  have hWscont (j : ℕ) : ContinuousOn (Ws j) (Icc a (a + δ)) := by
    obtain ⟨G, hG⟩ := hWspath j
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply G.continuous.congr
    intro t
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (hG t x).trans (hWs j t t.property x).symm
  let Vm (j : ℕ) : C(Icc a (a + δ), YR) := ⟨fun t => Vs j t, (hVscont j).domRestrict⟩
  let Gm (j : ℕ) : C(Icc a (a + δ), YR) := ⟨fun t => Ws j t, (hWscont j).domRestrict⟩
  let vm : C(Icc a (a + δ), YR) := ⟨fun t => v t, hvc.domRestrict⟩
  let gm : C(Icc a (a + δ), YR) := ⟨fun t => g t, hgc.domRestrict⟩
  have hVm : Tendsto Vm atTop (𝓝 vm) :=
    (hvc.tendsto_domRestrict_iff_tendstoUniformlyOn hVscont).mpr hVslim
  have hGm : Tendsto Gm atTop (𝓝 gm) :=
    (hgc.tendsto_domRestrict_iff_tendstoUniformlyOn hWscont).mpr hWslim
  obtain ⟨D, Z, d0, z0, hD, hZ, hDZrep, hdzrep, _hDZformula, _hdzformula, huniform⟩ :=
    exists_closed_embedded_threeJet_limits Fshort he hU heU hρ hρe cseq c0
      (fun j => m63C2_of_m62 (hcnshort (sigma j))) hc0short
      Rn Sn Hn Vm Gm r s h vm gm hRn hSn hHn hVm hGm hRrep hSrep hHrep
      (fun j t => hVs j t t.property) (fun j t => hWs j t t.property)
      (fun t x => (hfields t x).1.symm)
      (fun t x => (hfields t x).2.1.symm)
      (fun t x => (hfields t x).2.2.1.symm)
      (fun t x => (hfields t x).2.2.2.1.symm)
      (fun t x => (hfields t x).2.2.2.2.symm)
  refine ⟨sigma, hsigma, c0, hc0, hc0initial, ?_, Rn, D, Z, r, d0, z0,
    hRn, hD, hZ, ?_, ?_, huniform⟩
  · intro x
    exact hspeed0 x
  · intro j t x
    exact ⟨hRrep j t x, hDZrep j t x⟩
  · intro t x
    exact ⟨(hfields t x).1.symm, hdzrep t x⟩

end PoincareConjecture.M63
