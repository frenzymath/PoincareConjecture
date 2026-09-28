import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonNormalApproximants
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonNormalCurvatureBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralFamilyCompactJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.NormalLabelJacobianBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralLabelCompactness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralNormalGeometricFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.NormalSpeedFieldsLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.InitialCurvatureCap
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetAmbientBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "StateV" => State ((ℤ × Fin 2) × ι)
local notation "Y" => C(AddCircle curvePeriod, W)
local notation "YR" => C(AddCircle curvePeriod, ℝ)

theorem exists_common_normal_field_limits_of_unit_initial
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {γ : ℝ → M} (hγp : Function.Periodic γ L)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    (hunit : ∀ x, curveSpeed F (fun y _ => γ y) a x = 1) :
    let κ := L / curvePeriod
    ∃ δ : ℝ, ∃ hδ : 0 < δ, a + 2 * δ < b ∧
      ∃ R J : ℝ, 0 ≤ R ∧ 0 ≤ J ∧
      ∃ (cn : ℕ → ℝ → ℝ → M) (vinit : ℕ → ℝ),
        (∀ j, M63SmoothShrinkingCurveOn F (cn j) (Icc a (a + 2 * δ))) ∧
        (∀ j, vinit j ∈ Icc (κ / 2) (3 * κ / 2)) ∧
        Tendsto vinit atTop (𝓝 κ) ∧
        (∀ j x, curveSpeed F (cn j) a x = vinit j) ∧
        (∀ j t, t ∈ Icc a (a + 2 * δ) → ∀ x,
          m62CurvatureSquared F (cn j) t x ≤ R) ∧
        (∀ j t, t ∈ Ioc a (a + δ) → ∀ x,
          (F.metric t).tangentNorm (cn j x t) (m63CurvatureJet F (cn j) 1 t x) ≤
            J / Real.sqrt (t - a)) ∧
      ∃ (Rn Sn Hn : ℕ → C(Icc a (a + δ), Y)) (r s h : C(Icc a (a + δ), Y))
        (Vn Wn : ℕ → ℝ → YR) (v g : ℝ → YR),
        Tendsto Rn atTop (𝓝 r) ∧ Tendsto Sn atTop (𝓝 s) ∧ Tendsto Hn atTop (𝓝 h) ∧
        (∀ j (t : Icc a (a + δ)) (x : ℝ),
          Rn j t (x : AddCircle curvePeriod) = e (cn j x t)) ∧
        (∀ j (t : Icc a (a + δ)) (x : ℝ), Sn j t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (spatialUnitTangent F (cn j) t x)) ∧
        (∀ j (t : Icc a (a + δ)) (x : ℝ), Hn j t (x : AddCircle curvePeriod) =
          mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (m62CurvatureVector F (cn j) t x)) ∧
        (∀ j t, t ∈ Icc a (a + δ) → ∀ x : ℝ,
          Vn j t (x : AddCircle curvePeriod) = curveSpeed F (cn j) t x) ∧
        (∀ j t, t ∈ Icc a (a + δ) → ∀ x : ℝ,
          Wn j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (cn j) t) x) ∧
        ContinuousOn v (Icc a (a + δ)) ∧ ContinuousOn g (Icc a (a + δ)) ∧
        TendstoUniformlyOn Vn v atTop (Icc a (a + δ)) ∧
        TendstoUniformlyOn Wn g atTop (Icc a (a + δ)) ∧
        (∀ (t : Icc a (a + δ)) z, r t z ∈ U) ∧
        (∀ x : ℝ, r ⟨a, le_rfl, le_add_of_nonneg_right hδ.le⟩
          (x : AddCircle curvePeriod) = e (γ (κ * x))) ∧
        (∀ t ∈ Icc a (a + δ), ∀ x : ℝ, 0 < v t (x : AddCircle curvePeriod)) ∧
        v a = ContinuousMap.const _ κ ∧ g a = 0 := by
  classical
  dsimp only
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos Fact.out Real.two_pi_pos
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨T, hT, hTcap, _hT1, w, wn, m, u, psi, _hwn, hpath,
      hm, hmlim, _hqc, _hqxc, _hqp, hqzero, hqguard, hinit, hfamily⟩ :=
    exists_common_normal_approximants F he hU heU hρ hρe hγp hγ himm hunit
      (show 0 < (b - a) / 2 by linarith) (show (b - a) / 2 < b - a by linarith)
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := fun z : StateV => initialResponseTrace lambda z hT.le (u z)
  let q := initialResponseCurve (L := L) hT.le w (u w)
  let qn := fun j => initialResponseCurve (L := L) hT.le (wn j) (u (wn j))
  let c0 := fun x => e (γ x)
  let cn := fun j x t => ρ (qn j (t - a) (psi j (t - a) (κ * x)))
  have hqn (j : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (qn j)) (Icc 0 T ×ˢ univ) :=
    (hfamily j).1
  have hphase (j : ℕ) := (hfamily j).2.1
  have hqnp (j : ℕ) := (hfamily j).2.2.1
  have hqnguard (j : ℕ) := (hfamily j).2.2.2.1
  have hqnfixed (j : ℕ) := (hfamily j).2.2.2.2.1
  have hgspeed (j : ℕ) := (hfamily j).2.2.2.2.2.2.1
  have hlabels (j : ℕ) := (hfamily j).2.2.2.2.2.2.2
  have hpsi0 (j : ℕ) := (hlabels j).1
  have hpsishift (j : ℕ) := (hlabels j).2.1
  have hpsijoint (j : ℕ) := (hlabels j).2.2.1
  have hpsiode (j : ℕ) := (hlabels j).2.2.2.1
  have hpsipos (j : ℕ) := (hlabels j).2.2.2.2.1
  have hcn (j : ℕ) := (hlabels j).2.2.2.2.2.2.1
  have hcn0 (j : ℕ) : ∀ x, cn j x a = ρ (qn j 0 (κ * x)) :=
    (hlabels j).2.2.2.2.2.2.2.1
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hqslice (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (qn j t) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ => (t, x)) := contDiff_const.prodMk contDiff_id
    have hs := (hqn j).comp_contDiff hmap (fun _ => ⟨ht, mem_univ _⟩)
    exact hs
  have hc0 : ContDiff ℝ 2 c0 :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hγ).contDiff
  have hq0 : q 0 = c0 := funext hqzero
  have hc0guard (x : ℝ) : c0 x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c0 x) (deriv c0 x) ≠ 0 := by
    have hx := hqguard 0 hT0 x
    change q 0 x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q 0 x) (deriv (q 0) x) ≠ 0 at hx
    rwa [hq0] at hx
  obtain ⟨R0, hR0, hcap0⟩ := m63UniformInitialCurvatureSquared_bound F ha he hU heU hρ hρe
    hc0 (fun x => congrArg e (hγp x)) (fun j => qn j 0)
    (fun j => (hqslice j 0 hT0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun j => hqnp j 0) hc0guard (fun j => hqnguard j 0 hT0)
    (fun j => hqnfixed j 0 hT0) hinit
  have hinitialcap (j : ℕ) (x : ℝ) : m62CurvatureSquared F (cn j) a x ≤ R0 := by
    rw [curvatureSquared_congr_slice F (d := fun y (_ : ℝ) => ρ (qn j 0 (κ * y))) (hcn0 j)]
    exact hcap0 j κ hκ x
  have haT : a < a + T / 4 := by linarith only [hT]
  have hTb : a + T / 4 < b := by linarith only [hTcap, hT]
  obtain ⟨δ, hδ, hδT, hδ1, R, J, hR, hJ, hcap, hjet⟩ :=
    exists_common_normal_curvature_bounds F hcompact haT hTb.le cn hcn
      (show 0 ≤ R0 by linarith only [hR0]) hinitialcap
  have hδb : a + 2 * δ < b := hδT.trans_lt hTb
  have hδS : δ ≤ T / 4 := by linarith only [hδT, hδ]
  have hδT' : δ ≤ T := by linarith only [hδS, hT]
  have hsub : Icc (0 : ℝ) δ ⊆ Icc 0 T := Icc_subset_Icc_right hδT'
  have hsubS : Icc (0 : ℝ) δ ⊆ Icc 0 (T / 4) := Icc_subset_Icc_right hδS
  have haδ : a < a + δ := lt_add_of_pos_right a hδ
  have ha2δ : a < a + 2 * δ := by linarith only [hδ]
  have hwide : Icc a (a + 2 * δ) ⊆ Icc a (a + T / 4) := Icc_subset_Icc_right hδT
  have hshortwide : Icc a (a + δ) ⊆ Icc a (a + 2 * δ) :=
    Icc_subset_Icc_right (by linarith only [hδ])
  have hshort : Icc a (a + δ) ⊆ Icc a (a + T / 4) := hshortwide.trans hwide
  have hwideF : Icc a (a + 2 * δ) ⊆ Icc a b := Icc_subset_Icc_right hδb.le
  have hshortF : Icc a (a + δ) ⊆ Icc a b := hshortwide.trans hwideF
  let Fwide := m63RestrictClosedFlow F a (a + 2 * δ) hwideF ha2δ
  let Fshort := m63RestrictClosedFlow F a (a + δ) hshortF haδ
  have hcnwide (j : ℕ) : M62ShrinkingCurve Fwide (cn j) :=
    m63SmoothRestriction (hcn j) a (a + 2 * δ) hwide ha2δ
  have hcnshort (j : ℕ) : M62ShrinkingCurve Fshort (cn j) :=
    m63SmoothRestriction (hcn j) a (a + δ) hshort haδ
  obtain ⟨Kambient, hKambient, hBounds, _hRm, _hRic⟩ :=
    m63Exists_firstJet_ambient_bounds F hcompact
  have hBoundsShort : CurveEvolutionAmbientBounds Fshort Kambient Kambient Kambient :=
    m63RestrictAmbientBounds hBounds a (a + δ) hshortF haδ
  let inc : C(Icc (0 : ℝ) δ, Icc (0 : ℝ) T) :=
    ⟨fun t => ⟨t, hsub t.property⟩, continuous_subtype_val.subtype_mk _⟩
  let Vn := fun j => (V (wn j)).comp inc
  let V0 := (V w).comp inc
  have hVlim : Tendsto Vn atTop (𝓝 V0) := (inc.continuous_precomp.tendsto (V w)).comp hpath
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let jet := fun (z : StateV) (x : AddCircle L) =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  have hdecode (z : StateV) (t : Icc (0 : ℝ) δ) (x : ℝ) :
      jet ((V z).comp inc t) (x : AddCircle L) =
        (initialResponseCurve (L := L) hT.le z (u z) t x,
          deriv (initialResponseCurve (L := L) hT.le z (u z) t) x) := by
    have hproj : projIcc 0 T hT.le (t : ℝ) = inc t :=
      projIcc_of_mem hT.le (hsub t.property)
    apply Prod.ext
    · change _ = initialResponseCurve (L := L) hT.le z (u z) t x
      simp only [initialResponseCurve, hproj]
      rfl
    · have hd := (initialResponseCurve_spec (L := L) hT.le z (u z)).2.2.2 t x
      rw [hproj] at hd
      exact hd.deriv.symm
  have hnguard (j : ℕ) (t : Icc (0 : ℝ) δ) (x : AddCircle L) :
      (jet (Vn j t) x).1 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet (Vn j t) x).1 (jet (Vn j t) x).2 ≠ 0 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hdecode]
    exact hqnguard j t (hsub t.property) y
  have hguard0 (t : Icc (0 : ℝ) δ) (x : AddCircle L) :
      (jet (V0 t) x).1 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet (V0 t) x).1 (jet (V0 t) x).2 ≠ 0 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hdecode]
    exact hqguard t (hsub t.property) y
  obtain ⟨K, hK, hKU, _hK0, hKn, mu, Lambda, hmu, hLambda,
      _LA, _LB, _LD, hprincipal, _hAlip, _hBlip, _hDlip⟩ :=
    exists_compact_spectral_family_jet_domain F he hU hρ Vn V0 hVlim hnguard hguard0
  have hqmem (j : ℕ) (t : Icc (0 : ℝ) δ) (x : ℝ) :
      (qn j t x, deriv (qn j t) x) ∈ K := by
    have hx := hKn j t (x : AddCircle L)
    change jet (Vn j t) (x : AddCircle L) ∈ K at hx
    rwa [hdecode] at hx
  have hspatial (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun x => ρ (qn j t x)) := by
    intro x
    exact ((hρ.contMDiffAt (hU.mem_nhds (hqnguard j t ht x).1)).mdifferentiableAt
      (by simp)).comp x ((hqslice j t ht).contMDiff.mdifferentiable (by simp) x)
  have hvelocity (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      curveVelocity (n := n) (fun y => ρ (qn j t y)) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (deriv (qn j t) x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ qn j t) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hqnguard j t ht x).1)).mdifferentiableAt (by simp))
      ((hqslice j t ht).contMDiff.mdifferentiable (by simp) x),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have hinitspeed (j : ℕ) (x : ℝ) : curveSpeed F (cn j) a x = κ * m j := by
    calc
      _ = curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 (κ * y))) a x :=
        curveSpeed_congr_slice F (hcn0 j)
      _ = κ * curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 y)) a (κ * x) :=
        curveSpeed_comp F (fun y (_ : ℝ) => ρ (qn j 0 y)) (t := a) (x := x)
          (hspatial j 0 hT0 _) (by
          simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul κ) hκ.le
      _ = κ * m j := congrArg (κ * ·) (hgspeed j _)
  have hshiftmem (t : ℝ) (ht : t ∈ Icc a (a + δ)) : t - a ∈ Icc (0 : ℝ) δ :=
    ⟨sub_nonneg.mpr ht.1, by linarith only [ht.2]⟩
  have hpsislice (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T / 4)) :
      ContDiff ℝ ∞ (psi j t) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ => (t, x)) := contDiff_const.prodMk contDiff_id
    have hs := (hpsijoint j).comp_contDiff hmap (fun _ => ⟨ht, mem_univ _⟩)
    exact hs
  let ell := (1 / 2 : ℝ) * Real.exp (-(Kambient + R) * ((a + δ) - a)) * Real.sqrt mu
  let upper := (3 / 2 : ℝ) * Real.exp ((Kambient + R) * ((a + δ) - a)) * Real.sqrt Lambda
  have hlabelbounds (j : ℕ) : 0 < ell ∧ 0 < upper ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ x, ell ≤ deriv (psi j t) x ∧ deriv (psi j t) x ≤ upper := by
    have hb := normalLabel_derivative_bounds Fshort haδ
      (fun x t => ρ (qn j (t - a) x)) (fun t => psi j (t - a))
      hκ (hm j).1 (hm j).2 hmu hLambda hKambient hR hBoundsShort
      (fun t ht => hspatial j (t - a) (hsub (hshiftmem t ht)))
      (fun t ht x => by
        rw [hvelocity j (t - a) (hsub (hshiftmem t ht))]
        exact (hqnguard j (t - a) (hsub (hshiftmem t ht)) x).2)
      (fun t ht => (hpsislice j (t - a) (hsubS (hshiftmem t ht))).differentiable (by simp))
      (fun t ht => hpsipos j (t - a) (hsubS (hshiftmem t ht)))
      (fun x => by simpa only [sub_self] using hpsi0 j x)
      (fun x => by
        change curveSpeed F (fun y t => ρ (qn j (t - a) y)) a x = m j
        calc
          _ = curveSpeed F (fun y (_ : ℝ) => ρ (qn j 0 y)) a x :=
            curveSpeed_congr_slice F (fun y => by rw [sub_self])
          _ = m j := hgspeed j x)
      (fun t ht x => by
        have hp := hprincipal t (hshortF ht) _ (hqmem j ⟨t - a, hshiftmem t ht⟩ x)
        have heq : ambientCurvePrincipal F ρ t (qn j (t - a) x)
            (deriv (qn j (t - a)) x) =
              (curveSpeed Fshort (fun y s => ρ (qn j (s - a) y)) t x ^ 2)⁻¹ := by
          unfold ambientCurvePrincipal
          rw [← hvelocity j (t - a) (hsub (hshiftmem t ht))]
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
  have hphaseShort (j : ℕ) (t : Icc (0 : ℝ) δ) : DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0 :=
    (hphase j (inc t)).differentiableAt (by simp)
  obtain ⟨sigma, Dn, d, hsigma, hVseq, hDlim, hDrep, hd0⟩ :=
    exists_compact_spectral_label_displacements F hU hρ hδ
      (show δ < b - a by linarith only [hδb, hδ]) hK hKU Vn V0 hVlim qn
      (fun j => (hqn j).mono (prod_mono hsub Subset.rfl))
      (fun j t x => (congrArg Prod.fst (hdecode (wn j) t x)).symm)
      hphaseShort hKn psi
      (fun j => ((hpsijoint j).mono (prod_mono hsubS Subset.rfl)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
      (fun j t ht => hpsishift j t (hsubS ht)) hpsi0
      (fun j t ht x => (hpsiode j t (hsubS (Ioo_subset_Icc_self ht)) x).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hδS))) hell
      (fun j t ht x => ((hlabelbounds j).2.2 t ht x).1)
      (fun j t ht x => ((hlabelbounds j).2.2 t ht x).2)
  let cseq := fun j => cn (sigma j)
  let vinit := fun j => κ * m (sigma j)
  have hvinit (j : ℕ) : vinit j ∈ Icc (κ / 2) (3 * κ / 2) := by
    have hlo := mul_le_mul_of_nonneg_left (hm (sigma j)).1 hκ.le
    have hhi := mul_le_mul_of_nonneg_left (hm (sigma j)).2 hκ.le
    constructor <;> dsimp only [vinit] <;> linarith only [hlo, hhi]
  have hvlim : Tendsto vinit atTop (𝓝 κ) := by
    simpa only [vinit, Function.comp_def, mul_one] using
      (tendsto_const_nhds.mul (hmlim.comp hsigma.tendsto_atTop))
  have hm0 : 0 < κ / 2 := by positivity
  have hmV : κ / 2 ≤ 3 * κ / 2 := by linarith only [hκ]
  obtain ⟨Rn, Sn, Hn, r, s, h, hRn, hSn, hHn, hRrep, hSrep, hHrep, hrU, hr0⟩ :=
    exists_closed_normal_geometric_fields_of_spectral_family Fwide hcompact hδ
      (show δ ≤ 1 by linarith only [hδ1, hδ]) (show a + δ < a + 2 * δ by linarith)
      hR hm0 hmV he hU heU hρ hρe (fun j => Vn (sigma j)) V0 Dn d
      (fun j => psi (sigma j)) cseq vinit hVseq hDlim (fun j => hphaseShort (sigma j))
      (fun j t x => hnguard (sigma j) t (x : AddCircle L))
      (fun j t x => by
        have hd := congrArg Prod.fst (hdecode (wn (sigma j)) t x)
        change (jet (Vn (sigma j) t) (x : AddCircle L)).1 =
          e (ρ ((jet (Vn (sigma j) t) (x : AddCircle L)).1))
        rw [hd]
        exact hqnfixed (sigma j) t (hsub t.property) x)
      (fun t x => hguard0 t (x : AddCircle L))
      (by
        have hz : (fun x : ℝ => (jet (V0 ⟨0, le_rfl, hδ.le⟩) (x : AddCircle L)).1) = c0 := by
          funext x
          exact (congrArg Prod.fst (hdecode w ⟨0, le_rfl, hδ.le⟩ x)).trans (hqzero x)
        change ContDiff ℝ 2 (fun x : ℝ => (jet (V0 ⟨0, le_rfl, hδ.le⟩) (x : AddCircle L)).1)
        rw [hz]
        exact hc0)
      (by
        intro eps heps
        obtain ⟨N, hN⟩ := hinit eps heps
        refine ⟨N, fun j hj x => ?_⟩
        have hn : (fun y : ℝ => (jet (Vn (sigma j) ⟨0, le_rfl, hδ.le⟩)
            (y : AddCircle L)).1) = qn (sigma j) 0 :=
          funext fun y => congrArg Prod.fst (hdecode (wn (sigma j)) ⟨0, le_rfl, hδ.le⟩ y)
        have hz : (fun y : ℝ => (jet (V0 ⟨0, le_rfl, hδ.le⟩) (y : AddCircle L)).1) = c0 :=
          funext fun y => (congrArg Prod.fst (hdecode w ⟨0, le_rfl, hδ.le⟩ y)).trans (hqzero y)
        change ‖deriv (deriv (fun y : ℝ => (jet (Vn (sigma j) ⟨0, le_rfl, hδ.le⟩)
          (y : AddCircle L)).1)) x - deriv (deriv (fun y : ℝ =>
            (jet (V0 ⟨0, le_rfl, hδ.le⟩) (y : AddCircle L)).1)) x‖ < eps
        rw [hn, hz]
        exact (hN (sigma j) (hj.trans (hsigma.id_le j)) x).2.2)
      ell hell
      (fun j t => (hpsislice (sigma j) t (hsubS t.property)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
      (fun j t x => ((hlabelbounds (sigma j)).2.2 t t.property x).1) hDrep
      (fun j => hpsi0 (sigma j)) (fun j => hcnwide (sigma j)) hvinit
      (fun j => hinitspeed (sigma j))
      (fun j t ht => hcap (sigma j) t (Ioo_subset_Icc_self ht))
      (fun j t x => by
        change ρ (qn (sigma j) ((a + t) - a)
          (psi (sigma j) ((a + t) - a) (κ * x))) = _
        rw [add_sub_cancel_left]
        exact congrArg ρ (congrArg Prod.fst
          (hdecode (wn (sigma j)) t (psi (sigma j) t (κ * x)))).symm) hd0
  obtain ⟨Vs, Ws, v, g, hVs, hWs, hvc, hgc, hVslim, hWslim, hvbounds, hv0, hg0, _hvg⟩ :=
    exists_normal_speed_fields_limits Fshort haδ hcompact he hU heU hρ hρe
      hKambient hR hJ hBoundsShort hm0 hmV cseq (fun j => hcnshort (sigma j))
      vinit κ hvinit hvlim (fun j => hinitspeed (sigma j))
      (fun j t ht => hcap (sigma j) t (hshortwide (Ioo_subset_Icc_self ht)))
      (fun j t ht => hjet (sigma j) t (Ioo_subset_Ioc_self ht))
      Rn Sn Hn r s h hRn hSn hHn hRrep hSrep hHrep hrU
  refine ⟨δ, hδ, hδb, R, J, hR, hJ, cseq, vinit, ?_, hvinit, hvlim,
    fun j => hinitspeed (sigma j), fun j => hcap (sigma j), fun j => hjet (sigma j),
    Rn, Sn, Hn, r, s, h, Vs, Ws, v, g, hRn, hSn, hHn, hRrep, hSrep, hHrep,
    hVs, hWs, hvc, hgc, hVslim, hWslim, hrU, ?_, ?_, hv0, hg0⟩
  · intro j
    exact ⟨c2_restrict (hcn (sigma j)).1 hwide,
      (hcn (sigma j)).2.mono (prod_mono Subset.rfl (interior_mono hwide))⟩
  · intro x
    exact (hr0 x).trans ((congrArg Prod.fst
      (hdecode w ⟨0, le_rfl, hδ.le⟩ (κ * x))).trans (hqzero (κ * x)))
  · intro t ht x
    exact (mul_pos hm0 (Real.exp_pos _)).trans_le (hvbounds t ht x).1

end PoincareConjecture.M63
