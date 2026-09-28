import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable def reunionAxialCutoff (ε Z : ℝ) : ℝ :=
  Real.smoothTransition (-2 * Z / ε - 1)

theorem reunionAxialCutoff_spec (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (reunionAxialCutoff ε) ∧
    Antitone (reunionAxialCutoff ε) ∧
    (∀ Z : ℝ, reunionAxialCutoff ε Z ∈ Icc (0 : ℝ) 1) ∧
    (∀ Z : ℝ, deriv (reunionAxialCutoff ε) Z ≤ 0) ∧
    (∀ Z : ℝ, Z ≤ -ε → reunionAxialCutoff ε Z = 1) ∧
    ∀ Z : ℝ, -ε / 2 ≤ Z → reunionAxialCutoff ε Z = 0 := by
  have hs : ContDiff ℝ ∞ (reunionAxialCutoff ε) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const ε).sub contDiff_const)
  have hm : Antitone (reunionAxialCutoff ε) := by
    intro x y hxy
    apply Real.smoothTransition.monotone
    exact sub_le_sub_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonpos_left hxy (by norm_num)) hε.le) 1
  refine ⟨hs, hm, fun Z => ⟨Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩, fun Z => hm.deriv_nonpos, ?_, ?_⟩
  · intro Z hZ
    apply Real.smoothTransition.one_of_one_le
    have hdiv : (2 : ℝ) ≤ -2 * Z / ε :=
      (le_div_iff₀ hε).mpr (by nlinarith only [hZ])
    linarith only [hdiv]
  · intro Z hZ
    apply Real.smoothTransition.zero_of_nonpos
    have hdiv : -2 * Z / ε ≤ (1 : ℝ) :=
      (div_le_iff₀ hε).mpr (by nlinarith only [hZ])
    linarith only [hdiv]

noncomputable def reunionAxialHeight (a lambda ε t Z : ℝ) : ℝ :=
  lambda * Z - 2 * a * Real.smoothTransition t * reunionAxialCutoff ε Z

theorem reunionAxialHeight_spec (a lambda ε : ℝ)
    (ha : 0 < a) (hlambda : 0 < lambda) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => reunionAxialHeight a lambda ε p.1 p.2) ∧
    (∀ t Z : ℝ, HasDerivAt (reunionAxialHeight a lambda ε t)
      (lambda - 2 * a * Real.smoothTransition t * deriv (reunionAxialCutoff ε) Z) Z ∧
      lambda ≤ deriv (reunionAxialHeight a lambda ε t) Z) ∧
    (∀ t : ℝ, StrictMono (reunionAxialHeight a lambda ε t) ∧
      Function.Bijective (reunionAxialHeight a lambda ε t)) ∧
    (∀ t Z : ℝ, lambda * Z - 2 * a ≤ reunionAxialHeight a lambda ε t Z ∧
      reunionAxialHeight a lambda ε t Z ≤ lambda * Z) ∧
    (∀ t Z : ℝ, Z ≤ -ε → reunionAxialHeight a lambda ε t Z =
      lambda * Z - 2 * a * Real.smoothTransition t) ∧
    (∀ t Z : ℝ, -ε / 2 ≤ Z → reunionAxialHeight a lambda ε t Z = lambda * Z) ∧
    (∀ Z : ℝ, reunionAxialHeight a lambda ε 0 Z = lambda * Z) ∧
    ∀ Z : ℝ, reunionAxialHeight a lambda ε 1 Z =
      lambda * Z - 2 * a * reunionAxialCutoff ε Z := by
  obtain ⟨hχ, _hχmono, hχrange, hχderiv, hχone, hχzero⟩ :=
    reunionAxialCutoff_spec ε hε
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      reunionAxialHeight a lambda ε p.1 p.2) :=
    (contDiff_const.mul contDiff_snd).sub
      ((contDiff_const.mul (Real.smoothTransition.contDiff.comp contDiff_fst)).mul
        (hχ.comp contDiff_snd))
  have hd (t Z : ℝ) : HasDerivAt (reunionAxialHeight a lambda ε t)
      (lambda - 2 * a * Real.smoothTransition t * deriv (reunionAxialCutoff ε) Z) Z := by
    have hχd := ((hχ.differentiable (by simp)) Z).hasDerivAt
    simpa only [reunionAxialHeight, mul_one] using!
      ((hasDerivAt_id Z).const_mul lambda).sub
        (hχd.const_mul (2 * a * Real.smoothTransition t))
  have hdle (t Z : ℝ) : lambda ≤ deriv (reunionAxialHeight a lambda ε t) Z := by
    rw [(hd t Z).deriv]
    have hprod : 2 * a * Real.smoothTransition t * deriv (reunionAxialCutoff ε) Z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by positivity) (Real.smoothTransition.nonneg t)) (hχderiv Z)
    linarith only [hprod]
  have hbounds (t Z : ℝ) : lambda * Z - 2 * a ≤ reunionAxialHeight a lambda ε t Z ∧
      reunionAxialHeight a lambda ε t Z ≤ lambda * Z := by
    have hfactor0 : 0 ≤ Real.smoothTransition t * reunionAxialCutoff ε Z :=
      mul_nonneg (Real.smoothTransition.nonneg t) (hχrange Z).1
    have hfactor1 : Real.smoothTransition t * reunionAxialCutoff ε Z ≤ 1 := by
      calc
        Real.smoothTransition t * reunionAxialCutoff ε Z ≤
            1 * reunionAxialCutoff ε Z :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) (hχrange Z).1
        _ ≤ 1 := by simpa only [one_mul] using (hχrange Z).2
    dsimp only [reunionAxialHeight]
    constructor <;> nlinarith only [hfactor0, hfactor1, ha]
  have hbij (t : ℝ) : StrictMono (reunionAxialHeight a lambda ε t) ∧
      Function.Bijective (reunionAxialHeight a lambda ε t) := by
    have hm : StrictMono (reunionAxialHeight a lambda ε t) :=
      strictMono_of_deriv_pos (fun Z => hlambda.trans_le (hdle t Z))
    refine ⟨hm, hm.injective, ?_⟩
    intro w
    have hab : w / lambda ≤ (w + 2 * a) / lambda :=
      div_le_div_of_nonneg_right (by linarith only [ha]) hlambda.le
    have hlo : reunionAxialHeight a lambda ε t (w / lambda) ≤ w := by
      simpa only [mul_div_cancel₀ _ hlambda.ne'] using (hbounds t (w / lambda)).2
    have hhi : w ≤ reunionAxialHeight a lambda ε t ((w + 2 * a) / lambda) := by
      have h := (hbounds t ((w + 2 * a) / lambda)).1
      have heq : lambda * ((w + 2 * a) / lambda) = w + 2 * a := by field_simp
      rw [heq] at h
      linarith only [h]
    have hc : Continuous (reunionAxialHeight a lambda ε t) :=
      (hs.comp (contDiff_const.prodMk contDiff_id)).continuous
    obtain ⟨Z, _hZ, hZw⟩ := intermediate_value_Icc hab hc.continuousOn ⟨hlo, hhi⟩
    exact ⟨Z, hZw⟩
  refine ⟨hs, fun t Z => ⟨hd t Z, hdle t Z⟩, hbij, hbounds, ?_, ?_, ?_, ?_⟩
  · intro t Z hZ
    simp only [reunionAxialHeight, hχone Z hZ, mul_one]
  · intro t Z hZ
    simp only [reunionAxialHeight, hχzero Z hZ, mul_zero, sub_zero]
  · intro Z
    simp only [reunionAxialHeight, Real.smoothTransition.zero, mul_zero, zero_mul, sub_zero]
  · intro Z
    simp only [reunionAxialHeight, Real.smoothTransition.one, mul_one]

theorem exists_reunion_axial_spacetime_diffeomorph (a lambda ε : ℝ)
    (ha : 0 < a) (hlambda : 0 < lambda) (hε : 0 < ε) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      (∀ t Z : ℝ, D (t, Z) = (t, reunionAxialHeight a lambda ε t Z)) ∧
      ∀ t w : ℝ, (D.symm (t, w)).1 = t ∧
        reunionAxialHeight a lambda ε t (D.symm (t, w)).2 = w ∧
        w / lambda ≤ (D.symm (t, w)).2 ∧
        (D.symm (t, w)).2 ≤ (w + 2 * a) / lambda := by
  obtain ⟨hg, hderiv, hbij, hbounds, _htail, _hfixed, _hzero, _hone⟩ :=
    reunionAxialHeight_spec a lambda ε ha hlambda hε
  let g : ℝ × ℝ → ℝ := fun p => reunionAxialHeight a lambda ε p.1 p.2
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, g p)
  have hf : ContDiff ℝ ∞ f := contDiff_fst.prodMk hg
  have hfi : Function.Injective f := by
    rintro ⟨t, Z⟩ ⟨s, W⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    exact Prod.ext rfl ((hbij t).2.1 (congrArg Prod.snd h))
  have hfs : Function.Surjective f := by
    rintro ⟨t, w⟩
    obtain ⟨Z, hZ⟩ := (hbij t).2.2 w
    exact ⟨(t, Z), Prod.ext rfl hZ⟩
  have hd : ∀ p ∈ (univ : Set (ℝ × ℝ)),
      ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt f (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rintro ⟨t, Z⟩ _
    let L := fderiv ℝ g (t, Z)
    have hg' : HasFDerivAt g L (t, Z) :=
      ((hg.differentiable (by simp)) (t, Z)).hasFDerivAt
    let v := lambda - 2 * a * Real.smoothTransition t * deriv (reunionAxialCutoff ε) Z
    have hv : 0 < v := by
      have h := (hderiv t Z).2
      rw [(hderiv t Z).1.deriv] at h
      exact hlambda.trans_le h
    have hspatial : HasFDerivAt (reunionAxialHeight a lambda ε t)
        (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) Z :=
      hg'.comp Z (hasFDerivAt_prodMk_right t Z)
    have hLheight : L (0, 1) = v := by
      have h := hspatial.unique (hderiv t Z).1.hasFDerivAt
      simpa using congrArg (fun Q : ℝ →L[ℝ] ℝ => Q 1) h
    have hLformula (p : ℝ × ℝ) : L p = p.1 * L (1, 0) + p.2 * v := by
      calc
        L p = L (p.1 • (1, 0) + p.2 • (0, 1)) := by
          congr 1
          ext <;> simp
        _ = p.1 * L (1, 0) + p.2 * v := by
          simp only [map_add, map_smul, smul_eq_mul, hLheight]
    let A := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod L
    have hA : HasFDerivAt f A (t, Z) := hasFDerivAt_fst.prodMk hg'
    have hAi : Function.Injective A := by
      apply (injective_iff_map_eq_zero A).mpr
      intro p hp
      have hp1 : p.1 = 0 := congrArg Prod.fst hp
      have hp2 : p.2 = 0 := by
        have hz : L p = 0 := congrArg Prod.snd hp
        rw [hLformula, hp1, zero_mul, zero_add] at hz
        exact (mul_eq_zero.mp hz).resolve_right hv.ne'
      exact Prod.ext hp1 hp2
    have hAs : Function.Surjective A := by
      intro p
      refine ⟨(p.1, (p.2 - p.1 * L (1, 0)) / v), ?_⟩
      apply Prod.ext
      · rfl
      · change L (p.1, (p.2 - p.1 * L (1, 0)) / v) = p.2
        rw [hLformula]
        dsimp only
        rw [div_mul_cancel₀ _ hv.ne']
        ring
    obtain ⟨B, hB⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hAi, hAs⟩
    refine ⟨ContinuousLinearEquiv.ofUnit B, ?_⟩
    change HasFDerivAt f (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (t, Z)
    rw [hB]
    exact hA
  let e := smoothOpenChart f isOpen_univ hf.contDiffOn hd hfi.injOn
  have htgt : e.target = univ := by
    change f '' univ = univ
    ext p
    constructor
    · exact fun _ => mem_univ p
    · intro _
      obtain ⟨q, rfl⟩ := hfs p
      exact ⟨q, mem_univ q, rfl⟩
  have hei : ContDiff ℝ ∞ e.symm := by
    apply contDiffOn_univ.mp
    rw [← htgt]
    exact smoothOpenChart_symm_contDiffOn f isOpen_univ hf.contDiffOn hd hfi.injOn
  let D : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ := {
    toEquiv := {
      toFun := e
      invFun := e.symm
      left_inv := fun p => e.left_inv (mem_univ p)
      right_inv := fun p => e.right_inv (by rw [htgt]; exact mem_univ p) }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hei.contMDiff }
  refine ⟨D, fun _ _ => rfl, ?_⟩
  intro t w
  have heq : f (D.symm (t, w)) = (t, w) := D.apply_symm_apply (t, w)
  have ht : (D.symm (t, w)).1 = t := congrArg Prod.fst heq
  have hz : reunionAxialHeight a lambda ε t (D.symm (t, w)).2 = w := by
    have h := congrArg Prod.snd heq
    change reunionAxialHeight a lambda ε (D.symm (t, w)).1 (D.symm (t, w)).2 = w at h
    rwa [ht] at h
  obtain ⟨hlo, hhi⟩ := hbounds t (D.symm (t, w)).2
  rw [hz] at hlo hhi
  refine ⟨ht, hz, (div_le_iff₀ hlambda).mpr ?_, (le_div_iff₀ hlambda).mpr ?_⟩ <;>
    nlinarith only [hlo, hhi]

end PoincareConjecture.M25.Topology3D
