import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSupportedCutoff
import PoincareConjecture.Proofs.M25.Topology3D.Space3.TransverseSphereCollar
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.Algebra.SMul











set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold InnerProductSpace Topology BigOperators

namespace PoincareConjecture.M25.Topology3D




noncomputable def weightedSphereTimeMap
    (j N : UnitTwoSphere → E3) (A : Fin 2 → UnitTwoSphere × ℝ → E3)
    (eps : Fin 2 → ℝ) (w : Fin 2 → UnitTwoSphere → ℝ) :
    UnitTwoSphere × ℝ → E3 :=
  fun z => j z.1 +
    (∑ i : Fin 2, w i z.1 • (A i (z.1, eps i * z.2) - j z.1)) +
    ((1 - ∑ i : Fin 2, w i z.1) * z.2) • N z.1




theorem weightedSphereTimeMap_properties
    (j N : UnitTwoSphere → E3) (A : Fin 2 → UnitTwoSphere × ℝ → E3)
    (eps : Fin 2 → ℝ) (w : Fin 2 → UnitTwoSphere → ℝ)
    (V : Fin 2 → Set UnitTwoSphere) {eta : ℝ} (heta : 0 < eta)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hV : ∀ i, IsOpen (V i))
    (hA : ∀ i, ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ (A i)
      (V i ×ˢ Ioo (-eta) eta))
    (hzero : ∀ i p, p ∈ V i → A i (p, 0) = j p)
    (heps : ∀ i, |eps i| = 1)
    (hw : ∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (w i))
    (hsupport : ∀ i, tsupport (w i) ⊆ V i)
    (hrange : ∀ i p, w i p ∈ Icc 0 1)
    (hsum : ∀ p, (∑ i : Fin 2, w i p) ≤ 1) :
    let C := weightedSphereTimeMap j N A eps w
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ C
      (univ ×ˢ Ioo (-eta) eta) ∧
      (∀ p, C (p, 0) = j p) ∧
      (∀ p, deriv (fun s : ℝ => C (p, s)) 0 =
        (∑ i : Fin 2, w i p • (eps i • deriv (fun s : ℝ => A i (p, s)) 0)) +
        (1 - ∑ i : Fin 2, w i p) • N p) ∧
      ∀ i p, w i p = 1 → ∀ s : ℝ, C (p, s) = A i (p, eps i * s) := by
  classical
  let C := weightedSphereTimeMap j N A eps w
  have htime (i : Fin 2) {s : ℝ} (hs : s ∈ Ioo (-eta) eta) :
      eps i * s ∈ Ioo (-eta) eta := by
    apply abs_lt.mp
    rw [abs_mul, heps, one_mul]
    exact abs_lt.mpr hs
  have hterm (i : Fin 2) :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
        (fun z : UnitTwoSphere × ℝ =>
          w i z.1 • (A i (z.1, eps i * z.2) - j z.1))
        (univ ×ˢ Ioo (-eta) eta) := by
    apply contMDiffOn_sphere_supported_smul (w i) (hw i) (hV i) (hsupport i)
    have hparam : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : UnitTwoSphere × ℝ => (z.1, eps i * z.2)) :=
      contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
    exact ((hA i).comp hparam.contMDiffOn
      (fun z hz => ⟨hz.1, htime i hz.2⟩)).sub
        (hj.comp contMDiff_fst).contMDiffOn
  have hwtotal : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p => ∑ i : Fin 2, w i p) := by
    simp only [Fin.sum_univ_two]
    exact (hw 0).add (hw 1)
  have hnormal : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      (fun z : UnitTwoSphere × ℝ =>
        ((1 - ∑ i : Fin 2, w i z.1) * z.2) • N z.1) :=
    ((contMDiff_const.sub (hwtotal.comp contMDiff_fst)).mul contMDiff_snd).smul
      (hN.comp contMDiff_fst)
  have hC : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ C
      (univ ×ˢ Ioo (-eta) eta) := by
    unfold C weightedSphereTimeMap
    simp only [Fin.sum_univ_two]
    simp only [Fin.sum_univ_two] at hnormal
    exact (((hj.comp contMDiff_fst).contMDiffOn.add ((hterm 0).add (hterm 1))).add
      hnormal.contMDiffOn)
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro p
    have hz (i : Fin 2) : w i p • (A i (p, 0) - j p) = 0 := by
      by_cases hi : w i p = 0
      · simp only [hi, zero_smul]
      · rw [hzero i p (hsupport i (subset_tsupport (w i) hi)),
          sub_self, smul_zero]
    simp only [weightedSphereTimeMap, mul_zero, hz, Finset.sum_const_zero,
      zero_smul, add_zero]
  · intro p
    have hdterm (i : Fin 2) : HasDerivAt
        (fun s : ℝ => w i p • (A i (p, eps i * s) - j p))
        (w i p • (eps i • deriv (fun s : ℝ => A i (p, s)) 0)) 0 := by
      by_cases hi : w i p = 0
      · simpa only [hi, zero_smul] using hasDerivAt_const (0 : ℝ) (0 : E3)
      · have hp : p ∈ V i := hsupport i (subset_tsupport (w i) hi)
        have hAi := (hA i).contMDiffAt (((hV i).prod isOpen_Ioo).mem_nhds
          (show (p, (0 : ℝ)) ∈ V i ×ˢ Ioo (-eta) eta from
            ⟨hp, neg_lt_zero.mpr heta, heta⟩))
        have hslice : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) ∞
            (fun s : ℝ => A i (p, s)) 0 :=
          hAi.comp 0 (contMDiffAt_const.prodMk contMDiffAt_id)
        have hd0 : HasDerivAt (fun s : ℝ => A i (p, s))
            (deriv (fun s : ℝ => A i (p, s)) 0) (eps i * 0) := by
          simpa only [mul_zero] using
            (hslice.contDiffAt.differentiableAt (by simp)).hasDerivAt
        have hscale := hd0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul (eps i))
        have hd := (hscale.sub_const (j p)).const_smul (w i p)
        simp only [mul_one, Function.comp_def] at hd
        exact hd
    have hdsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => hdterm i)
    have hdnormal : HasDerivAt
        (fun s : ℝ => ((1 - ∑ i : Fin 2, w i p) * s) • N p)
        ((1 - ∑ i : Fin 2, w i p) • N p) 0 := by
      simpa only [mul_one, id_eq] using
        (((hasDerivAt_id (0 : ℝ)).const_mul (1 - ∑ i : Fin 2, w i p)).smul_const (N p))
    have hdC := ((hasDerivAt_const (0 : ℝ) (j p)).add hdsum).add hdnormal
    have hdC' : HasDerivAt (fun s : ℝ => weightedSphereTimeMap j N A eps w (p, s))
        (0 + (∑ i : Fin 2, w i p • (eps i • deriv (fun s : ℝ => A i (p, s)) 0)) +
          (1 - ∑ i : Fin 2, w i p) • N p) 0 := hdC
    simpa only [zero_add] using hdC'.deriv
  · intro i p hi s
    have hs := hsum p
    rw [Fin.sum_univ_two] at hs
    fin_cases i
    · change w 0 p = 1 at hi
      have hother : w 1 p = 0 := by linarith [(hrange 1 p).1]
      simp only [weightedSphereTimeMap, Fin.sum_univ_two, hi, hother,
        one_smul, zero_smul, add_zero, sub_self, zero_mul]
      abel
    · change w 1 p = 1 at hi
      have hother : w 0 p = 0 := by linarith [(hrange 0 p).1]
      simp only [weightedSphereTimeMap, Fin.sum_univ_two, hi, hother,
        one_smul, zero_smul, zero_add, add_zero, sub_self, zero_mul]
      abel




theorem exists_weighted_sphere_collar
    (j N : UnitTwoSphere → E3) (A : Fin 2 → UnitTwoSphere × ℝ → E3)
    (eps : Fin 2 → ℝ) (w : Fin 2 → UnitTwoSphere → ℝ)
    (V : Fin 2 → Set UnitTwoSphere) {eta : ℝ} (heta : 0 < eta)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hinj : Function.Injective j)
    (himm : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j p))
    (hunit : ∀ p, ‖N p‖ = 1)
    (horth : ∀ p (v : TangentSpace (𝓡 2) p),
      ⟪N p, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0)
    (hV : ∀ i, IsOpen (V i))
    (hA : ∀ i, ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ (A i)
      (V i ×ˢ Ioo (-eta) eta))
    (hzero : ∀ i p, p ∈ V i → A i (p, 0) = j p)
    (heps : ∀ i, |eps i| = 1)
    (hpos : ∀ i p, p ∈ V i →
      0 < ⟪N p, eps i • deriv (fun s : ℝ => A i (p, s)) 0⟫_ℝ)
    (hw : ∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (w i))
    (hsupport : ∀ i, tsupport (w i) ⊆ V i)
    (hrange : ∀ i p, w i p ∈ Icc 0 1)
    (hsum : ∀ p, (∑ i : Fin 2, w i p) ≤ 1)
    {W : Set E3} (hW : IsOpen W) (hjW : range j ⊆ W)
    {b : ℝ} (hb : 0 < b) :
    let C := weightedSphereTimeMap j N A eps w
    ∃ tau0 > (0 : ℝ), tau0 < min b eta ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
        IsCollarEmbedding (fun z : UnitTwoSphere × ℝ => C (z.1, tau * z.2)) ∧
        (∀ p, C (p, tau * 0) = j p) ∧
        (∀ z ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)),
          (z.1, tau * z.2) ∈ univ ×ˢ Ioo (-eta) eta) ∧
        MapsTo (fun z : UnitTwoSphere × ℝ => C (z.1, tau * z.2))
          (univ ×ˢ Ioo (-1) 1) W ∧
        ∀ i p, w i p = 1 → ∀ s : ℝ, |s| < 1 →
          C (p, tau * s) = A i (p, eps i * tau * s) := by
  let C := weightedSphereTimeMap j N A eps w
  obtain ⟨hC, hcentral, hvelocity, hpatch⟩ := weightedSphereTimeMap_properties
    j N A eps w V heta hj hN hV hA hzero heps hw hsupport hrange hsum
  have htrans (p : UnitTwoSphere) :
      0 < ⟪N p, deriv (fun s : ℝ => C (p, s)) 0⟫_ℝ := by
    let a : Fin 2 → ℝ := fun i =>
      ⟪N p, eps i • deriv (fun s : ℝ => A i (p, s)) 0⟫_ℝ
    have ha (i : Fin 2) (hi : w i p ≠ 0) : 0 < a i :=
      hpos i p (hsupport i (subset_tsupport (w i) hi))
    have hnonneg (i : Fin 2) : 0 ≤ w i p * a i := by
      by_cases hi : w i p = 0
      · simp only [hi, zero_mul, le_refl]
      · exact mul_nonneg (hrange i p).1 (ha i hi).le
    have hs : w 0 p + w 1 p ≤ 1 := by simpa only [Fin.sum_univ_two] using hsum p
    have hpositive : 0 < w 0 p * a 0 + w 1 p * a 1 + (1 - (w 0 p + w 1 p)) := by
      by_cases h0 : w 0 p = 0
      · by_cases h1 : w 1 p = 0
        · simp only [h0, h1, zero_mul, zero_add, sub_zero, zero_lt_one]
        · have hw1 : 0 < w 1 p := lt_of_le_of_ne (hrange 1 p).1 (Ne.symm h1)
          have hp1 := mul_pos hw1 (ha 1 h1)
          linarith [hnonneg 0]
      · have hw0 : 0 < w 0 p := lt_of_le_of_ne (hrange 0 p).1 (Ne.symm h0)
        have hp0 := mul_pos hw0 (ha 0 h0)
        linarith [hnonneg 1]
    rw [hvelocity]
    simpa only [Fin.sum_univ_two, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hunit, one_pow, mul_one, a] using hpositive
  let B : Set (UnitTwoSphere × ℝ) := univ ×ˢ Ioo (-eta) eta
  let U : Set (UnitTwoSphere × ℝ) := B ∩ C ⁻¹' W
  have hB : IsOpen B := isOpen_univ.prod isOpen_Ioo
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hB hW
  have hzeroU (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ U := by
    refine ⟨⟨mem_univ _, neg_lt_zero.mpr heta, heta⟩, ?_⟩
    change weightedSphereTimeMap j N A eps w (p, 0) ∈ W
    rw [hcentral]
    exact hjW (mem_range_self p)
  have hfull (p : UnitTwoSphere) :
      Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0)) := by
    have hd : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0) :=
      (hC.contMDiffAt (hB.mem_nhds (hzeroU p).1)).mdifferentiableAt (by simp)
    apply sphere_product_mfderiv_bijective_of_normal C j hcentral p hd (himm p)
      (N p) (horth p)
    rw [mfderiv_sphere_product_time C p hd]
    exact (htrans p).ne'
  obtain ⟨tau0, htau0, hsmall, hcollar⟩ := exists_transverse_sphere_collar C j hU
    hzeroU (hC.mono inter_subset_left) hcentral hinj hfull (lt_min hb heta)
  refine ⟨tau0, htau0, hsmall, ?_⟩
  intro tau htau htau_le
  obtain ⟨hemb, hmem, hcenter⟩ := hcollar tau htau htau_le
  refine ⟨hemb, hcenter, fun z hz => (hmem z hz).1,
    fun z hz => (hmem z hz).2, ?_⟩
  intro i p hp s _
  simpa only [mul_assoc] using hpatch i p hp (tau * s)

end PoincareConjecture.M25.Topology3D
