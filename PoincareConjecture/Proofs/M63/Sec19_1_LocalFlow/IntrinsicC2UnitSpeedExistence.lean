import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonNormalFieldExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.NormalFieldC2Reconstruction
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedCurvatureJetLimits
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedCurvatureJetIdentification
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicRegularityFromSpatialLimits
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.UniformUpperCutoffJetBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "YR" => C(AddCircle curvePeriod, ℝ)




theorem exists_intrinsic_c2_local_curve_of_unit_initial
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {L : ℝ} (hL : 0 < L) {γ : ℝ → M} (hγp : Function.Periodic γ L)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    (hunit : ∀ x, curveSpeed F (fun y _ => γ y) a x = 1) :
    ∃ T : ℝ, a < T ∧ T < b ∧ ∃ c : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Icc a T) ∧
      (∀ x, c x a = γ ((L / curvePeriod) * x)) ∧
      M63IntrinsicRegularityOn F c (Icc a T) := by
  classical
  let : Fact (0 < L) := ⟨hL⟩
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos hL Real.two_pi_pos
  obtain ⟨δ, hδ, hδb, R, J, hR, hJ, cn, vinit, hcn, hvinit, hvinitlim,
      hinitial, hcap, hjet, Rn, Sn, Hn, r, sigma, h, Vn, Wn, v, g,
      hRn, hSn, hHn, hRrep, hSrep, hHrep, hVrep, hWrep,
      hv, hg, hV, hW, hrU, hr0, hvpos, _hv0, _hg0⟩ :=
    exists_common_normal_field_limits_of_unit_initial F hab hcompact
      he hU heU hρ hρe hγp hγ himm hunit
  have haT : a < a + δ := lt_add_of_pos_right a hδ
  have haB : a < a + 2 * δ := by linarith only [hδ]
  have hTB : a + δ < a + 2 * δ := by linarith only [hδ]
  have hTb : a + δ < b := hTB.trans hδb
  have hwideF : Icc a (a + 2 * δ) ⊆ Icc a b := Icc_subset_Icc_right hδb.le
  have hshortF : Icc a (a + δ) ⊆ Icc a b := Icc_subset_Icc_right hTb.le
  have hshortwide : Icc a (a + δ) ⊆ Icc a (a + 2 * δ) :=
    Icc_subset_Icc_right hTB.le
  let Fwide := m63RestrictClosedFlow F a (a + 2 * δ) hwideF haB
  let Fshort := m63RestrictClosedFlow F a (a + δ) hshortF haT
  have hcnwide (j : ℕ) : M62ShrinkingCurve Fwide (cn j) :=
    m63SmoothRestriction (hcn j) a (a + 2 * δ) Subset.rfl haB
  have hcnshort (j : ℕ) : M62ShrinkingCurve Fshort (cn j) :=
    m63SmoothRestriction (hcn j) a (a + δ) hshortwide haT
  obtain ⟨K, hK, hBounds, _hRm, _hRic⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  have hBoundsShort : CurveEvolutionAmbientBounds Fshort K K K :=
    m63RestrictAmbientBounds hBounds a (a + δ) hshortF haT
  have hcapshort (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a (a + δ)) (x : ℝ) :
      m62CurvatureSquared Fshort (cn j) t x ≤ R :=
    hcap j t (hshortwide (Ioo_subset_Icc_self ht)) x
  let c : ℝ → ℝ → M := fun x t =>
    ρ (r (projIcc a (a + δ) haT.le t) (x : AddCircle curvePeriod))
  obtain ⟨hcshort, hfields, _hinitSpeed, hprimitive⟩ :=
    normalField_c2_reconstruction_with_anchored_speed Fshort haT
      he hU heU hρ hρe hK hR hBoundsShort (half_pos hκ)
      (show κ / 2 ≤ 3 * κ / 2 by linarith only [hκ]) cn hcnshort vinit κ
      hvinit hvinitlim hinitial hcapshort Rn Sn Hn r sigma h hRn hSn hHn
      hRrep hSrep hHrep hrU Vn Wn v g hVrep hWrep hv hg hV hW hvpos
  have hc : M63C2ShrinkingCurveOn F c (Icc a (a + δ)) := {
    domain_subset := hshortF
    periodic := hcshort.periodic
    spatial_regular := hcshort.spatial_regular
    joint_c1 := hcshort.joint_c1
    immersed := hcshort.immersed
    continuous := hcshort.continuous
    velocity_continuous := hcshort.velocity_continuous
    curvature_continuous := hcshort.curvature_continuous
    equation := hcshort.equation }
  have hc0 (x : ℝ) : c x a = γ (κ * x) := by
    change ρ (r (projIcc a (a + δ) haT.le a) (x : AddCircle curvePeriod)) = _
    rw [projIcc_of_mem haT.le ⟨le_rfl, haT.le⟩, hr0, hρe]
  let Vmax := (3 * κ / 2) * Real.exp ((K + R) * δ)
  let B0 := K + 2 * K * Real.sqrt R
  let B1 := 4 * Real.sqrt R * J
  let Gmax := Vmax ^ 2 * (B0 * δ + B1 * Real.sqrt δ)
  have hVmax : 0 ≤ Vmax := by dsimp only [Vmax]; positivity
  have hB0 : 0 ≤ B0 := by dsimp only [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp only [B1]; positivity
  have hGmax : 0 ≤ Gmax := by dsimp only [Gmax]; positivity
  have hinitialpos (j : ℕ) : 0 < vinit j := (half_pos hκ).trans_le (hvinit j).1
  have hve (j : ℕ) : vinit j * Real.exp ((K + R) * δ) ≤ Vmax :=
    mul_le_mul_of_nonneg_right (hvinit j).2 (Real.exp_pos _).le
  have hspeed (j : ℕ) (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      |curveSpeed F (cn j) t x| + |deriv (curveSpeed F (cn j) t) x| ≤ Vmax + Gmax := by
    have hage : t - a ≤ δ := by linarith only [ht.2]
    have hage0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hspeed0 := (curveSpeed_exp_bounds Fshort (cn j) (hcnshort j)
      hBoundsShort x (fun u hu => hcapshort j u hu x) ⟨le_rfl, haT.le⟩ ht ht.1).2
    change curveSpeed F (cn j) t x ≤
      curveSpeed F (cn j) a x * Real.exp ((K + R) * (t - a)) at hspeed0
    rw [hinitial] at hspeed0
    have hspeed1 : curveSpeed F (cn j) t x ≤ Vmax :=
      hspeed0.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hage (add_nonneg hK hR))) (hinitialpos j).le).trans
          (hve j))
    have hgrad := curveSpeed_spatial_abs_bound Fshort (cn j) (hcnshort j)
      hK hR hJ (hinitialpos j) hBoundsShort (hinitial j) (hcapshort j)
      (fun u hu y => hjet j u ⟨hu.1, hu.2.le⟩ y) ht x
    have hspan : a + δ - a = δ := by ring
    rw [hspan] at hgrad
    have hcoeff : B0 * (t - a) + B1 * Real.sqrt (t - a) ≤
        B0 * δ + B1 * Real.sqrt δ :=
      add_le_add (mul_le_mul_of_nonneg_left hage hB0)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hage) hB1)
    have hgrad1 : |deriv (curveSpeed F (cn j) t) x| ≤ Gmax :=
      hgrad.trans (mul_le_mul
        (pow_le_pow_left₀ (mul_nonneg (hinitialpos j).le (Real.exp_pos _).le) (hve j) 2)
        hcoeff (by positivity) (sq_nonneg _))
    rw [abs_of_nonneg (M62.speed_nonneg F (cn j) t x)]
    exact add_le_add hspeed1 hgrad1
  have hquot : IsOpenQuotientMap
      (fun z : Icc a (a + δ) × ℝ => (z.1, (z.2 : AddCircle curvePeriod))) :=
    IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
  have hVcont (j : ℕ) : ContinuousOn (Vn j) (Icc a (a + δ)) := by
    have hlift : ContinuousOn (fun z : ℝ × ℝ => Vn j z.2 (z.1 : AddCircle curvePeriod))
        (univ ×ˢ Icc a (a + δ)) :=
      (M62.speed_continuousOn Fshort (cn j) (hcnshort j)).congr
        (fun z hz => hVrep j z.2 hz.2 z.1)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hquot.continuous_comp_iff.mp
      (hlift.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun z => ⟨mem_univ _, z.1.2⟩))
  let Vm (j : ℕ) : C(Icc a (a + δ), YR) := ⟨fun t => Vn j t, (hVcont j).domRestrict⟩
  let vm : C(Icc a (a + δ), YR) := ⟨fun t => v t, hv.domRestrict⟩
  have hVm : Tendsto Vm atTop (𝓝 vm) :=
    (hv.tendsto_domRestrict_iff_tendstoUniformlyOn hVcont).mpr hV
  have hjetwide (j i : ℕ) (t x : ℝ) :
      m63CurvatureJet Fwide (cn j) i t x = m63CurvatureJet F (cn j) i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F (cn j) t
        (fun y => m63CurvatureJet Fwide (cn j) i t y) x =
        m62SpatialDerivative F (cn j) t (fun y => m63CurvatureJet F (cn j) i t y) x
      rw [show (fun y => m63CurvatureJet Fwide (cn j) i t y) =
        (fun y => m63CurvatureJet F (cn j) i t y) from funext ih]
  have hslab (tau s : ℝ) (hat : a < tau) (hts : tau < s) (hsT : s ≤ a + δ) :
      (∀ i (t : Icc tau s), ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M))) ∧
      ∀ i, ContinuousOn (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Icc tau s) := by
    have hsub : Icc tau s ⊆ Icc a (a + δ) :=
      fun _ ht => ⟨hat.le.trans ht.1, ht.2.trans hsT⟩
    let inc : C(Icc tau s, Icc a (a + δ)) :=
      ⟨fun t => ⟨t, hsub t.property⟩, continuous_subtype_val.subtype_mk _⟩
    have hjets : ∀ i : ℕ, ∃ Ki : ℝ, 0 ≤ Ki ∧ ∀ j (t : Icc tau s) (x : ℝ),
        (Fwide.metric t).tangentNorm (cn j x t) (m63CurvatureJet Fwide (cn j) i t x) ≤ Ki := by
      intro i
      obtain ⟨Ci, _hCi, hCiBound⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff
        F hcompact i (alpha := a) (B := a + 2 * δ) (R := R) (delta := tau - a)
        le_rfl haB hδb.le hR (sub_pos.mpr hat)
      refine ⟨Real.sqrt Ci, Real.sqrt_nonneg _, ?_⟩
      intro j t x
      rw [hjetwide]
      change Real.sqrt (m63CurvatureJetSquared F (cn j) i t x) ≤ Real.sqrt Ci
      apply Real.sqrt_le_sqrt
      exact hCiBound (a + 2 * δ) haB le_rfl (cn j) (hcn j)
        (fun u hu y => hcap j u (Ioo_subset_Icc_self hu) y) t
        ⟨hat.trans_le t.2.1, (t.2.2.trans hsT).trans_lt hTB⟩
        (sub_le_sub_right t.2.1 a) x
    have hvpos' (t : Icc tau s) (z : AddCircle curvePeriod) : 0 < vm.comp inc t z := by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact hvpos t (hsub t.property) x
    obtain ⟨_G, η, hzero, _hGrep, _hGlim, hrec⟩ :=
      exists_closed_embeddedCurvatureJet_limits Fwide hcompact hat hts (hsT.trans_lt hTB)
        he hU heU hρ hρe cn hcnwide
        (fun j => (Rn j).comp inc) (fun j => (Sn j).comp inc)
        (fun j => (Hn j).comp inc) (fun j => (Vm j).comp inc)
        (r.comp inc) (sigma.comp inc) (h.comp inc) (vm.comp inc)
        ((inc.continuous_precomp.tendsto r).comp hRn)
        ((inc.continuous_precomp.tendsto sigma).comp hSn)
        ((inc.continuous_precomp.tendsto h).comp hHn)
        ((inc.continuous_precomp.tendsto vm).comp hVm)
        (fun j t x => hRrep j (inc t) x) (fun j t x => hSrep j (inc t) x)
        (fun j t x => hHrep j (inc t) x) (fun j t x => hVrep j t (hsub t.property) x)
        (fun t z => hrU (inc t) z) hvpos' hjets
        ⟨Vmax + Gmax, add_nonneg hVmax hGmax,
          fun j t x => hspeed j t (hsub t.property) x⟩
    have hzero' (t : Icc tau s) (x : ℝ) : η 0 t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) := by
      rw [hzero]
      exact (hfields (inc t) x).2.2.1.symm
    have hid := curvatureJet_identification_of_embedded_recurrences F hat hts
      (hsT.trans hTb.le) he hU heU hρ hρe (c2_restrict hc hsub) η hzero' (by
        intro i t x
        have hd := hrec i t x
        change HasDerivAt (fun y : ℝ => η i t (y : AddCircle curvePeriod))
          (v t (x : AddCircle curvePeriod) •
            (η (i + 1) t (x : AddCircle curvePeriod) +
              coordinateHessian (F.connection t) e (ρ (r (inc t) (x : AddCircle curvePeriod)))
                (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r (inc t) (x : AddCircle curvePeriod))
                  (sigma (inc t) (x : AddCircle curvePeriod)))
                (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r (inc t) (x : AddCircle curvePeriod))
                  (η i t (x : AddCircle curvePeriod))))) x at hd
        have hp : e (c x t) = r (inc t) (x : AddCircle curvePeriod) :=
          (hfields (inc t) x).1
        have hs : (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) : W) =
            sigma (inc t) (x : AddCircle curvePeriod) := (hfields (inc t) x).2.1
        have hv' : curveSpeed F c t x = v t (x : AddCircle curvePeriod) :=
          (hfields (inc t) x).2.2.2.1
        erw [← hp, ← hs, ← hv'] at hd
        exact hd)
    exact ⟨hid.2.1, hid.2.2⟩
  refine ⟨a + δ, haT, hTb, c, hc, hc0, ?_⟩
  apply intrinsic_regularity_of_spatial_jets_and_speed_primitive F haT hc
    he hU heU hρ hρe
  · intro i t hat htT
    have hmid : a < (a + t) / 2 := by linarith only [hat]
    have hmidt : (a + t) / 2 < t := by linarith only [hat]
    exact (hslab ((a + t) / 2) t hmid hmidt htT).1 i ⟨t, hmidt.le, le_rfl⟩
  · intro tau s hat hts hsT i
    have hmid : a < (a + tau) / 2 := by linarith only [hat]
    have hmidtau : (a + tau) / 2 < tau := by linarith only [hat]
    exact ((hslab ((a + tau) / 2) s hmid (hmidtau.trans_le hts) hsT).2 i).mono
      (prod_mono Subset.rfl (Icc_subset_Icc_left hmidtau.le))
  · intro tau t hat htt htT x
    exact hprimitive tau t hat.le htt htT x

end PoincareConjecture.M63
