import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapCoordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def stackProfileBlend {X : Type*} (f0 f1 : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  (1 - Real.smoothTransition t) * f0 x + Real.smoothTransition t * f1 x

theorem stackProfileBlend_contDiff {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f0 f1 : X → ℝ) (h0 : ContDiff ℝ ∞ f0) (h1 : ContDiff ℝ ∞ f1) :
    ContDiff ℝ ∞ (fun p : ℝ × X => stackProfileBlend f0 f1 p.1 p.2) :=
  ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul
    (h0.comp contDiff_snd)).add
      ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (h1.comp contDiff_snd))

theorem stackProfileBlend_pos {X : Type*} (f0 f1 : X → ℝ) (t : ℝ) (x : X)
    (h0 : 0 < f0 x) (h1 : 0 < f1 x) : 0 < stackProfileBlend f0 f1 t x := by
  by_cases h : Real.smoothTransition t = 1
  · simpa only [stackProfileBlend, h, sub_self, zero_mul, one_mul, zero_add] using h1
  · have ht : Real.smoothTransition t < 1 :=
      lt_of_le_of_ne (Real.smoothTransition.le_one t) h
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) h0)
      (mul_nonneg (Real.smoothTransition.nonneg t) h1.le)

theorem stackProfileBlend_le {X : Type*} (f0 f1 : X → ℝ) (t : ℝ) (x : X) (L : ℝ)
    (h0 : f0 x ≤ L) (h1 : f1 x ≤ L) : stackProfileBlend f0 f1 t x ≤ L := by
  calc
    stackProfileBlend f0 f1 t x ≤
        (1 - Real.smoothTransition t) * L + Real.smoothTransition t * L :=
      add_le_add (mul_le_mul_of_nonneg_left h0
        (sub_nonneg.mpr (Real.smoothTransition.le_one t)))
        (mul_le_mul_of_nonneg_left h1 (Real.smoothTransition.nonneg t))
    _ = L := by ring

theorem stackProfileBlend_of_nonpos {X : Type*} (f0 f1 : X → ℝ)
    (t : ℝ) (ht : t ≤ 0) (x : X) : stackProfileBlend f0 f1 t x = f0 x := by
  simp only [stackProfileBlend, Real.smoothTransition.zero_of_nonpos ht,
    sub_zero, one_mul, zero_mul, add_zero]

theorem stackProfileBlend_of_one_le {X : Type*} (f0 f1 : X → ℝ)
    (t : ℝ) (ht : 1 ≤ t) (x : X) : stackProfileBlend f0 f1 t x = f1 x := by
  simp only [stackProfileBlend, Real.smoothTransition.one_of_one_le ht,
    sub_self, zero_mul, one_mul, zero_add]

theorem stackProfileBlend_eq_of_eq {X : Type*} (f0 f1 : X → ℝ)
    (t : ℝ) (x : X) (h : f0 x = f1 x) : stackProfileBlend f0 f1 t x = f0 x := by
  unfold stackProfileBlend
  rw [← h]
  ring

noncomputable def stackCapProfilePath (a0 a1 : ℝ → ℝ) (b0 b1 : E2 → ℝ)
    (t : ℝ) (p : E2 × ℝ) : E2 × ℝ :=
  let x := stackProfileBlend a0 a1 t p.2 • p.1
  (x, stackProfileBlend b0 b1 t x * p.2)

noncomputable def stackCapProfilePathDiffeomorph
    (a0 a1 : ℝ → ℝ) (b0 b1 : E2 → ℝ)
    (ha0 : ContDiff ℝ ∞ a0) (ha1 : ContDiff ℝ ∞ a1)
    (hb0 : ContDiff ℝ ∞ b0) (hb1 : ContDiff ℝ ∞ b1)
    (hapos0 : ∀ v, 0 < a0 v) (hapos1 : ∀ v, 0 < a1 v)
    (hbpos0 : ∀ x, 0 < b0 x) (hbpos1 : ∀ x, 0 < b1 x) :
    Diffeomorph 𝓘(ℝ, ℝ × (E2 × ℝ)) 𝓘(ℝ, ℝ × (E2 × ℝ))
      (ℝ × (E2 × ℝ)) (ℝ × (E2 × ℝ)) ∞ := by
  let A := stackProfileBlend a0 a1
  let B := stackProfileBlend b0 b1
  have hAne (t v : ℝ) : A t v ≠ 0 :=
    (stackProfileBlend_pos a0 a1 t v (hapos0 v) (hapos1 v)).ne'
  have hBne (t : ℝ) (x : E2) : B t x ≠ 0 :=
    (stackProfileBlend_pos b0 b1 t x (hbpos0 x) (hbpos1 x)).ne'
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) :=
    stackProfileBlend_contDiff a0 a1 ha0 ha1
  have hB : ContDiff ℝ ∞ (fun p : ℝ × E2 => B p.1 p.2) :=
    stackProfileBlend_contDiff b0 b1 hb0 hb1
  refine {
    toEquiv := {
      toFun := fun p => (p.1, stackCapProfilePath a0 a1 b0 b1 p.1 p.2)
      invFun := fun p =>
        let v := (B p.1 p.2.1)⁻¹ * p.2.2
        (p.1, ((A p.1 v)⁻¹ • p.2.1, v))
      left_inv := ?_
      right_inv := ?_ }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · rintro ⟨t, x, v⟩
    change (t, ((A t ((B t (A t v • x))⁻¹ * (B t (A t v • x) * v)))⁻¹ •
      (A t v • x), (B t (A t v • x))⁻¹ * (B t (A t v • x) * v))) = (t, x, v)
    rw [← mul_assoc, inv_mul_cancel₀ (hBne t (A t v • x)), one_mul,
      smul_smul, inv_mul_cancel₀ (hAne t v), one_smul]
  · rintro ⟨t, x, v⟩
    change (t, (A t ((B t x)⁻¹ * v) • ((A t ((B t x)⁻¹ * v))⁻¹ • x),
      B t (A t ((B t x)⁻¹ * v) • ((A t ((B t x)⁻¹ * v))⁻¹ • x)) *
        ((B t x)⁻¹ * v))) = (t, x, v)
    rw [smul_smul, mul_inv_cancel₀ (hAne t ((B t x)⁻¹ * v)), one_smul,
      ← mul_assoc, mul_inv_cancel₀ (hBne t x), one_mul]
  · have hAv : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => A p.1 p.2.2) :=
      hA.comp (contDiff_fst.prodMk contDiff_snd.snd)
    have hX : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => A p.1 p.2.2 • p.2.1) :=
      hAv.smul contDiff_snd.fst
    exact (contDiff_fst.prodMk
      (hX.prodMk ((hB.comp (contDiff_fst.prodMk hX)).mul contDiff_snd.snd))).contMDiff
  · have hBX : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => B p.1 p.2.1) :=
      hB.comp (contDiff_fst.prodMk contDiff_snd.fst)
    have hV : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (B p.1 p.2.1)⁻¹ * p.2.2) :=
      (hBX.inv (fun p => hBne p.1 p.2.1)).mul contDiff_snd.snd
    have hAV : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) =>
        A p.1 ((B p.1 p.2.1)⁻¹ * p.2.2)) :=
      hA.comp (contDiff_fst.prodMk hV)
    exact (contDiff_fst.prodMk
      (((hAV.inv (fun p => hAne p.1 ((B p.1 p.2.1)⁻¹ * p.2.2))).smul
        contDiff_snd.fst).prodMk hV)).contMDiff

variable (a0 a1 : ℝ → ℝ) (b0 b1 : E2 → ℝ)
variable (ha0 : ContDiff ℝ ∞ a0) (ha1 : ContDiff ℝ ∞ a1)
variable (hb0 : ContDiff ℝ ∞ b0) (hb1 : ContDiff ℝ ∞ b1)
variable (hapos0 : ∀ v, 0 < a0 v) (hapos1 : ∀ v, 0 < a1 v)
variable (hbpos0 : ∀ x, 0 < b0 x) (hbpos1 : ∀ x, 0 < b1 x)

@[simp] theorem stackCapProfilePathDiffeomorph_apply (t : ℝ) (p : E2 × ℝ) :
    stackCapProfilePathDiffeomorph a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 (t, p) =
        (t, stackCapProfilePath a0 a1 b0 b1 t p) := rfl

@[simp] theorem stackCapProfilePathDiffeomorph_symm_apply (t : ℝ) (p : E2 × ℝ) :
    (stackCapProfilePathDiffeomorph a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1).symm (t, p) =
        (t, ((stackProfileBlend a0 a1 t ((stackProfileBlend b0 b1 t p.1)⁻¹ * p.2))⁻¹ •
          p.1, (stackProfileBlend b0 b1 t p.1)⁻¹ * p.2)) := rfl

theorem stackCapProfilePathDiffeomorph_time (p : ℝ × (E2 × ℝ)) :
    (stackCapProfilePathDiffeomorph a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 p).1 = p.1 := rfl

theorem stackCapProfilePath_eq_flatCapDiffeomorph (t : ℝ) (p : E2 × ℝ) :
    stackCapProfilePath a0 a1 b0 b1 t p =
      flatCapDiffeomorph (stackProfileBlend a0 a1 t) (stackProfileBlend b0 b1 t)
        ((stackProfileBlend_contDiff a0 a1 ha0 ha1).comp
          (contDiff_const.prodMk contDiff_id))
        ((stackProfileBlend_contDiff b0 b1 hb0 hb1).comp
          (contDiff_const.prodMk contDiff_id))
        (fun v => (stackProfileBlend_pos a0 a1 t v (hapos0 v) (hapos1 v)).ne')
        (fun x => (stackProfileBlend_pos b0 b1 t x (hbpos0 x) (hbpos1 x)).ne') p := rfl

include ha0 ha1 hb0 hb1 in

theorem stackCapProfilePath_native_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2 × ℝ) ∞
      (fun p : ℝ × UnitTwoSphere =>
        stackCapProfilePath a0 a1 b0 b1 p.1 (heightCoordinates (p.2 : E3))) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ ((↑) : UnitTwoSphere → E3) :=
    contMDiff_coe_sphere
  have hCs : ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞
      (fun q : UnitTwoSphere => heightCoordinates (q : E3)) :=
    heightCoordinates.contDiff.contMDiff.comp hi
  have hQ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (Prod.snd : ℝ × UnitTwoSphere → UnitTwoSphere) := contMDiff_snd
  have hC : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2 × ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => heightCoordinates (p.2 : E3)) :=
    hCs.comp hQ
  have hT : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × UnitTwoSphere → ℝ) := contMDiff_fst
  have hz : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => (heightCoordinates (p.2 : E3)).2) :=
    contDiff_snd.comp_contMDiff hC
  have hx : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitTwoSphere => (heightCoordinates (p.2 : E3)).1) :=
    contDiff_fst.comp_contMDiff hC
  have hS : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => Real.smoothTransition p.1) :=
    Real.smoothTransition.contDiff.comp_contMDiff hT
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × UnitTwoSphere =>
        stackProfileBlend a0 a1 p.1 (heightCoordinates (p.2 : E3)).2) :=
    ((contMDiff_const.sub hS).mul (ha0.comp_contMDiff hz)).add
      (hS.mul (ha1.comp_contMDiff hz))
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitTwoSphere => stackProfileBlend a0 a1 p.1
        (heightCoordinates (p.2 : E3)).2 • (heightCoordinates (p.2 : E3)).1) := hA.smul hx
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => stackProfileBlend b0 b1 p.1
        (stackProfileBlend a0 a1 p.1 (heightCoordinates (p.2 : E3)).2 •
          (heightCoordinates (p.2 : E3)).1)) :=
    ((contMDiff_const.sub hS).mul (hb0.comp_contMDiff hX)).add
      (hS.mul (hb1.comp_contMDiff hX))
  exact hX.prodMk_space (hB.mul hz)

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 in

theorem stackCapProfilePath_fst_norm_le
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (t : ℝ) (p : E2 × ℝ) (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1) :
    ‖(stackCapProfilePath a0 a1 b0 b1 t p).1‖ ≤ 1 := by
  rw [stackCapProfilePath_eq_flatCapDiffeomorph a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1]
  exact flatCapDiffeomorph_fst_norm_le _ _ _ _ _ _
    (fun v => stackProfileBlend_pos a0 a1 t v (hapos0 v) (hapos1 v))
    (fun v hv => stackProfileBlend_le a0 a1 t v _ (habound0 v hv) (habound1 v hv)) p hp

include hbpos0 hbpos1 in

theorem stackCapProfilePath_snd_nonpos (t : ℝ) (p : E2 × ℝ) (hp : p.2 ≤ 0) :
    (stackCapProfilePath a0 a1 b0 b1 t p).2 ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos
    (stackProfileBlend_pos b0 b1 t _ (hbpos0 _) (hbpos1 _)).le hp

include hbpos0 hbpos1 in

theorem stackCapProfilePath_snd_neg_iff (t : ℝ) (p : E2 × ℝ) :
    (stackCapProfilePath a0 a1 b0 b1 t p).2 < 0 ↔ p.2 < 0 := by
  change stackProfileBlend b0 b1 t (stackProfileBlend a0 a1 t p.2 • p.1) * p.2 < 0 ↔ _
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ (stackProfileBlend_pos b0 b1 t _ (hbpos0 _) (hbpos1 _))
      (b := p.2) (c := 0))

include ha0 ha1 hb0 hb1 in

theorem exists_stackCapProfilePath_height_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, ∀ q : UnitTwoSphere,
      |(stackCapProfilePath a0 a1 b0 b1 t (heightCoordinates (q : E3))).2| ≤ C := by
  have hF : Continuous (fun p : ℝ × UnitTwoSphere =>
      (stackCapProfilePath a0 a1 b0 b1 p.1 (heightCoordinates (p.2 : E3))).2) :=
    (stackCapProfilePath_native_contMDiff a0 a1 b0 b1 ha0 ha1 hb0 hb1).continuous.snd
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (univ : Set UnitTwoSphere)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (q : UnitTwoSphere) :
      |(stackCapProfilePath a0 a1 b0 b1 s (heightCoordinates (q : E3))).2| ≤ max 1 C0 := by
    have h : |(stackCapProfilePath a0 a1 b0 b1 s (heightCoordinates (q : E3))).2| ≤ C0 := by
      simpa only [Real.norm_eq_abs] using hC0 (s, q) ⟨hs, mem_univ q⟩
    exact h.trans (le_max_right _ _)
  refine ⟨max 1 C0, le_max_left _ _, fun t q => ?_⟩
  by_cases ht : t ≤ 0
  · simpa only [stackCapProfilePath, stackProfileBlend,
      Real.smoothTransition.zero_of_nonpos ht,
      Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))] using
        hbound 0 ⟨le_rfl, zero_le_one⟩ q
  · by_cases ht1 : 1 ≤ t
    · simpa only [stackCapProfilePath, stackProfileBlend,
        Real.smoothTransition.one_of_one_le ht1,
        Real.smoothTransition.one_of_one_le (le_refl (1 : ℝ))] using
          hbound 1 ⟨zero_le_one, le_rfl⟩ q
    · exact hbound t ⟨(lt_of_not_ge ht).le, (lt_of_not_ge ht1).le⟩ q

theorem exists_stackCapProfilePath_common_ambient_germ
    (delta : ℝ) (hdelta : 0 < delta)
    (W : Set E2) (hW : IsOpen W) (hcircle : sphere (0 : E2) 1 ⊆ W)
    (ha0near : ∀ v, |v| < delta → a0 v = (Real.sqrt (1 - v ^ 2))⁻¹)
    (ha1near : ∀ v, |v| < delta → a1 v = (Real.sqrt (1 - v ^ 2))⁻¹)
    (hb0near : ∀ x ∈ W, b0 x = 1) (hb1near : ∀ x ∈ W, b1 x = 1) :
    ∃ O : Set (E2 × ℝ), IsOpen O ∧ sphere (0 : E2) 1 ×ˢ ({0} : Set ℝ) ⊆ O ∧
      (∀ t : ℝ, ∀ p ∈ O, stackCapProfilePath a0 a1 b0 b1 t p =
        ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2)) ∧
      ∀ t : ℝ, ∀ p ∈ O, stackCapProfilePath a0 a1 b0 b1 t p =
        stackCapProfilePath a0 a1 b0 b1 0 p := by
  let d := min delta (1 / 2)
  have hd : 0 < d := lt_min hdelta (by norm_num)
  let U : Set (E2 × ℝ) := {p | |p.2| < d}
  let aStar : ℝ → ℝ := fun v => (Real.sqrt (1 - v ^ 2))⁻¹
  have hU : IsOpen U := isOpen_lt continuous_snd.abs continuous_const
  have hrad (p : E2 × ℝ) (hp : p ∈ U) : 0 < 1 - p.2 ^ 2 := by
    have hsmall : |p.2| < 1 / 2 := lt_of_lt_of_le hp (min_le_right _ _)
    nlinarith [sq_abs p.2, abs_nonneg p.2]
  have hStar : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => aStar p.2) U :=
    ((contDiffOn_const.sub (contDiff_snd.pow 2).contDiffOn).sqrt
      (fun p hp => (hrad p hp).ne')).inv
      (fun p hp => (Real.sqrt_pos.mpr (hrad p hp)).ne')
  have hF : ContinuousOn (fun p : E2 × ℝ => aStar p.2 • p.1) U :=
    (hStar.smul contDiff_fst.contDiffOn).continuousOn
  let O := U ∩ (fun p : E2 × ℝ => aStar p.2 • p.1) ⁻¹' W
  have hO : IsOpen O := hF.isOpen_inter_preimage hU hW
  have hequator : sphere (0 : E2) 1 ×ˢ ({0} : Set ℝ) ⊆ O := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    subst v
    refine ⟨?_, ?_⟩
    · simpa only [U, mem_ofPred_eq, abs_zero] using hd
    · simpa only [mem_preimage, aStar, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
        Real.sqrt_one, inv_one, one_smul] using hcircle hx
  have heq (t : ℝ) (p : E2 × ℝ) (hp : p ∈ O) :
      stackCapProfilePath a0 a1 b0 b1 t p = (aStar p.2 • p.1, p.2) := by
    have hv : |p.2| < delta := lt_of_lt_of_le hp.1 (min_le_left _ _)
    have hA : stackProfileBlend a0 a1 t p.2 = aStar p.2 := by
      rw [stackProfileBlend, ha0near p.2 hv, ha1near p.2 hv]
      dsimp [aStar]
      ring
    have hB : stackProfileBlend b0 b1 t (aStar p.2 • p.1) = 1 := by
      rw [stackProfileBlend, hb0near _ hp.2, hb1near _ hp.2]
      ring
    simp only [stackCapProfilePath, hA, hB, one_mul]
  exact ⟨O, hO, hequator, heq, fun t p hp => (heq t p hp).trans (heq 0 p hp).symm⟩

end PoincareConjecture.M25.Topology3D
