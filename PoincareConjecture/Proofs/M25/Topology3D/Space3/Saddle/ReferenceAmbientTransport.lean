import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceRadialField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ExteriorFlowBarrier
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold InnerProductSpace Topology Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_ambient_transport
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (a : ℝ) (ha : 0 < a) (haCorrection : 16 / sigma < a ^ 2)
    (haLarge : 8 < a ^ 2)
    (u : UnitTwoSphere) (c rho : ℝ) (hrho : 0 < rho)
    (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hheight : ∀ p : UnitTwoSphere,
      ⟪(u : E3), F (p : E3)⟫_ℝ = c + rho ^ 2 * a ^ 2 *
        (1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
          d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2))) :
    let RF3 := exists_nonnested_reference_exterior_coordinates
      sigma hsigma hsigmaSmall d hd hdNear hdZero hdBounds hdDeriv
      a ha haCorrection haLarge
    let Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere :=
      Classical.choose (Classical.choose_spec RF3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let nu : ℝ := rho ^ 2 * a ^ 2
    let b : ℝ := 1 / (128 * a ^ 2)
    let f : UnitTwoSphere → ℝ := fun p =>
      1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
        d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
    let q : UnitTwoSphere → ℝ := fun p =>
      ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
    let j : UnitTwoSphere → E3 := fun p => F (p : E3)
    let S : Set E3 := range j
    let eps : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let Z : Fin 4 → ℝ → ℝ → E3 := fun k h R =>
      !₂[sx k * Real.sqrt (R ^ 2 / a ^ 2 + h),
        sy k * Real.sqrt (R ^ 2 / a ^ 2 - h),
        -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)]
    let T : Fin 2 → Set E3 := fun i => {y : E3 |
      1 / 2 < ‖F.symm y‖ ∧ ‖F.symm y‖ < 3 / 2 ∧
        sphereDirection (F.symm y) ∈ (Q i).target}
    let E : ℝ → Set E3 := fun h =>
      j '' {p : UnitTwoSphere | f p = h ∧ 2 / a ^ 2 ≤ q p}
    let Ei : Fin 2 → ℝ → Set E3 := fun i h =>
      j '' {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧
        f p = h ∧ 2 / a ^ 2 ≤ q p}
    ∃ (zeta : ℝ) (X : E3 → E3) (K B : ℝ≥0)
      (hK : LipschitzWith K X) (hB : ∀ y, ‖X y‖ ≤ B)
      (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X),
    let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
      fun t => boundedFlowDiffeomorph X hK hB hX hcX t
    ∃ C : Set E3,
      0 < zeta ∧ zeta < 1 / 8 ∧ IsCompact C ∧ tsupport X ⊆ C ∧
      C ⊆ (⋃ i : Fin 2, T i) ∩ {y : E3 | |H y - c| < 4 * nu * b} ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
      (∀ y : E3, Phi 0 y = y) ∧
      (∀ t : ℝ, ∀ y : E3,
        Phi t y = boundedFlow X hK hB y t ∧
        (Phi t).symm y = boundedFlow X hK hB y (-t)) ∧
      (∀ t : ℝ,
        tsupport (fun y : E3 => Phi t y - y) ⊆ C ∧
        tsupport (fun y : E3 => (Phi t).symm y - y) ⊆ C) ∧
      (∀ (t : ℝ) (y : E3),
        ‖F.symm (Phi t y)‖ = ‖F.symm y‖ ∧
        ‖F.symm ((Phi t).symm y)‖ = ‖F.symm y‖) ∧
      (∀ t : ℝ,
        Phi t '' (F '' ball (0 : E3) 1) = F '' ball (0 : E3) 1 ∧
        Phi t '' (F '' closedBall (0 : E3) 1) = F '' closedBall (0 : E3) 1 ∧
        Phi t '' S = S ∧ (Phi t).symm '' S = S) ∧
      (∀ (i : Fin 2) (t : ℝ),
        Phi t '' T i = T i ∧ (Phi t).symm '' T i = T i) ∧
      (∀ (t : ℝ) (y : E3),
        (q (sphereDirection (F.symm y)) ≤ 1 / (8 * a ^ 2) ∨
          4 * nu * b ≤ |H y - c| ∨ y ∉ ⋃ i : Fin 2, T i) →
        Phi t y = y ∧ (Phi t).symm y = y) ∧
      (∀ p : UnitTwoSphere, |f p| ≤ 3 * b → 2 / a ^ 2 ≤ q p →
        H (X (j p)) = 1) ∧
      (∀ h : ℝ, |h| ≤ 3 * b →
        (∀ (i : Fin 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
          (t, h) ∈ (Q i).source) ∧
        (∀ i : Fin 2, Ei i h = (fun t : ℝ => j (Q i (t, h))) '' Icc (0 : ℝ) 1) ∧
        E h = Ei 0 h ∪ Ei 1 h ∧ Disjoint (Ei 0 h) (Ei 1 h)) ∧
      (∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ h : ℝ, |h| ≤ 3 * b →
          ‖Z k h R‖ = 1 ∧ H (F (Z k h R)) = c + nu * h) ∧
      (∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ (h s : ℝ), |h| ≤ 2 * b → |s| ≤ zeta →
          HasDerivAt (fun t : ℝ => F ((1 + s) • Z k (t / nu) R))
            (X (F ((1 + s) • Z k h R))) (nu * h)) ∧
      (∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ (h0 h1 s : ℝ), |h0| ≤ 2 * b → |h1| ≤ 2 * b → |s| ≤ zeta →
          Phi (nu * (h1 - h0)) (F ((1 + s) • Z k h0 R)) =
            F ((1 + s) • Z k h1 R) ∧
          (Phi (nu * (h1 - h0))).symm (F ((1 + s) • Z k h1 R)) =
            F ((1 + s) • Z k h0 R)) ∧
      ∀ h0 h1 : ℝ, |h0| ≤ 2 * b → |h1| ≤ 2 * b →
        (∀ i : Fin 2,
          Phi (nu * (h1 - h0)) '' Ei i h0 = Ei i h1 ∧
          (Phi (nu * (h1 - h0))).symm '' Ei i h1 = Ei i h0) ∧
        Phi (nu * (h1 - h0)) '' E h0 = E h1 ∧
        (Phi (nu * (h1 - h0))).symm '' E h1 = E h0 := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let RF3 := exists_nonnested_reference_exterior_coordinates
    sigma hsigma hsigmaSmall d hd hdNear hdZero hdBounds hdDeriv a ha haCorrection haLarge
  let Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere :=
    Classical.choose (Classical.choose_spec RF3)
  obtain ⟨_heta, _hetaSmall, hQall, _hProduct, _hClosed, _hRegular, hCompare, hQends⟩ :=
    Classical.choose_spec (Classical.choose_spec RF3)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let nu : ℝ := rho ^ 2 * a ^ 2
  let b : ℝ := 1 / (128 * a ^ 2)
  let f : UnitTwoSphere → ℝ := fun p =>
    1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  let q : UnitTwoSphere → ℝ := fun p => ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
  let j : UnitTwoSphere → E3 := fun p => F (p : E3)
  let S : Set E3 := range j
  let eps : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let Z : Fin 4 → ℝ → ℝ → E3 := fun k h R =>
    !₂[sx k * Real.sqrt (R ^ 2 / a ^ 2 + h),
      sy k * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)]
  let T : Fin 2 → Set E3 := fun i => {y : E3 | 1 / 2 < ‖F.symm y‖ ∧
    ‖F.symm y‖ < 3 / 2 ∧ sphereDirection (F.symm y) ∈ (Q i).target}
  let E : ℝ → Set E3 := fun h => j '' {p : UnitTwoSphere | f p = h ∧ 2 / a ^ 2 ≤ q p}
  let Ei : Fin 2 → ℝ → Set E3 := fun i h =>
    j '' {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧ f p = h ∧ 2 / a ^ 2 ≤ q p}
  obtain ⟨zeta, Xi, Ci, hzeta, hzetaSmall, hTdis, hXi, hRad, hUnit,
    hCover, hZ, hDer⟩ := exists_nonnested_reference_radial_field
    sigma hsigma hsigmaSmall d hd hdNear hdZero hdBounds hdDeriv
    a ha haCorrection haLarge u c rho hrho F hheight
  let X : E3 → E3 := fun y => Xi 0 y + Xi 1 y
  change ∀ h : ℝ, |h| ≤ 3 * b →
    (∀ (i : Fin 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → (t, h) ∈ (Q i).source) ∧
    (∀ i : Fin 2, Ei i h = (fun t : ℝ => j (Q i (t, h))) '' Icc (0 : ℝ) 1) ∧
    E h = Ei 0 h ∪ Ei 1 h ∧ Disjoint (Ei 0 h) (Ei 1 h) at hCover
  change ∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
    ∀ (h s : ℝ), |h| ≤ 2 * b → |s| ≤ zeta →
      HasDerivAt (fun t : ℝ => F ((1 + s) • Z k (t / nu) R))
        (X (F ((1 + s) • Z k h R))) (nu * h) at hDer
  let C : Set E3 := Ci 0 ∪ Ci 1
  have hC : IsCompact C := (hXi 0).2.2.1.union (hXi 1).2.2.1
  have hXiZ (i : Fin 2) (y : E3) (hy : y ∉ T i) : Xi i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hy ((hXi i).2.2.2.2
      ((hXi i).2.2.2.1 hh)).1)
  have hXZ (y : E3) (hy : y ∉ C) : X y = 0 := by
    have h0 : Xi 0 y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hy (Or.inl ((hXi 0).2.2.2.1 hh)))
    have h1 : Xi 1 y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hy (Or.inr ((hXi 1).2.2.2.1 hh)))
    simp only [X, h0, h1, add_zero]
  have hXs : tsupport X ⊆ C :=
    closure_minimal (fun y hy => by by_contra hn; exact hy (hXZ y hn)) hC.isClosed
  have hX : ContDiff ℝ ∞ X := (hXi 0).1.add (hXi 1).1
  have hcX : HasCompactSupport X := hC.of_isClosed_subset (isClosed_tsupport X) hXs
  have hCsub : C ⊆ (⋃ i : Fin 2, T i) ∩ {y : E3 | |H y - c| < 4 * nu * b} := by
    intro y hy
    rcases hy with hy | hy
    · exact ⟨mem_iUnion.mpr ⟨0, ((hXi 0).2.2.2.2 hy).1⟩,
        ((hXi 0).2.2.2.2 hy).2⟩
    · exact ⟨mem_iUnion.mpr ⟨1, ((hXi 1).2.2.2.2 hy).1⟩,
        ((hXi 1).2.2.2.2 hy).2⟩
  obtain ⟨K, B, hK, hB⟩ := compactField_bounds X hX hcX
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph X hK hB hX hcX t
  have hPhi (t : ℝ) (y : E3) : Phi t y = boundedFlow X hK hB y t := rfl
  have hPhii (t : ℝ) (y : E3) : (Phi t).symm y = boundedFlow X hK hB y (-t) := rfl
  have hJoint := boundedFlow_contDiff X hK hB hX hcX
  have hPhiSmooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) :=
    hJoint.comp (contDiff_snd.prodMk contDiff_fst)
  have hPhiISmooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) :=
    hJoint.comp (contDiff_snd.prodMk contDiff_fst.neg)
  have hSupport (t : ℝ) :
      tsupport (fun y => boundedFlow X hK hB y t - y) ⊆ C :=
    closure_minimal ((boundedFlow_support_subset X hK hB t).trans
      ((subset_tsupport X).trans hXs)) hC.isClosed
  have hnu : 0 < nu := mul_pos (sq_pos_of_pos hrho) (sq_pos_of_pos ha)
  have hb : 0 < b := by dsimp [b]; positivity
  have hdelta : 0 < nu * b := mul_pos hnu hb
  have hj : Continuous j := F.continuous.comp continuous_subtype_val
  have hji : Injective j := fun p p' hh => Subtype.ext (F.injective hh)
  have hJH (p : UnitTwoSphere) : H (j p) = c + nu * f p := hheight p
  have hdir (p : UnitTwoSphere) : sphereDirection (F.symm (j p)) = p := by
    rw [show F.symm (j p) = (p : E3) from F.symm_apply_apply _]
    simpa only [one_smul] using sphereDirection_smul p (by norm_num : (0 : ℝ) < 1)
  have hQt (i : Fin 2) : (Q i).target = {p : UnitTwoSphere |
      f p ∈ Ioo (-4 * b) (4 * b) ∧ 0 < eps i * (p : E3) 1 ∧
        1 / (8 * a ^ 2) < q p} := (hQall i).2.1
  have hQH (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ (Q i).source) : f (Q i z) = z.2 := by
    apply (hQall i).2.2.2.2.2.2 z
    have hsrc := (hQall i).1
    change (Q i).source = _ at hsrc
    rwa [← hsrc]
  let Ann : Set E3 := {y | 1 / 2 < ‖F.symm y‖ ∧ ‖F.symm y‖ < 3 / 2}
  have hAnnZ (y : E3) (hy : y ∉ Ann) : X y = 0 := by
    apply hXZ y
    intro hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCsub hh).1
    exact hy ⟨hi.1, hi.2.1⟩
  have hRadius (y : E3) (t : ℝ) :
      ‖F.symm (boundedFlow X hK hB y t)‖ = ‖F.symm y‖ := by
    by_cases hy : y ∈ Ann
    · apply boundedFlow_preserves_firstIntegral X hK hB hAnnZ
        (fun z : E3 => ‖F.symm z‖) ?_ (fun z _ => hRad z) y hy t
      intro z hz
      exact ((contDiffAt_norm ℝ (by
        intro heq
        have hn := hz.1
        rw [heq, norm_zero] at hn
        linarith)).comp z F.symm.contDiff.contDiffAt).differentiableAt (by simp)
    · rw [boundedFlow_eq_self X hK hB y (hAnnZ y hy) t]
  have hImage (A : Set E3)
      (hA : ∀ y ∈ A, ∀ t : ℝ, boundedFlow X hK hB y t ∈ A) (t : ℝ) :
      Phi t '' A = A := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact hA z hz t
    · intro y hy
      refine ⟨boundedFlow X hK hB y (-t), hA y hy (-t), ?_⟩
      simpa only [hPhi, neg_neg] using boundedFlow_neg X hK hB y (-t)
  have hBall (y : E3) : y ∈ F '' ball (0 : E3) 1 ↔ ‖F.symm y‖ < 1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [F.symm_apply_apply, mem_ball_zero_iff] using hz
    · intro hy
      exact ⟨F.symm y, mem_ball_zero_iff.mpr hy, F.apply_symm_apply y⟩
  have hClosedBall (y : E3) : y ∈ F '' closedBall (0 : E3) 1 ↔ ‖F.symm y‖ ≤ 1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [F.symm_apply_apply, mem_closedBall_zero_iff] using hz
    · intro hy
      exact ⟨F.symm y, mem_closedBall_zero_iff.mpr hy, F.apply_symm_apply y⟩
  have hSphere (y : E3) : y ∈ S ↔ ‖F.symm y‖ = 1 := by
    constructor
    · rintro ⟨p, rfl⟩
      simpa only [j, F.symm_apply_apply] using norm_eq_of_mem_sphere p
    · intro hy
      exact ⟨⟨F.symm y, mem_sphere_zero_iff_norm.mpr hy⟩, F.apply_symm_apply y⟩
  have hSflow (y : E3) (hy : y ∈ S) (t : ℝ) : boundedFlow X hK hB y t ∈ S := by
    rw [hSphere, hRadius]
    exact (hSphere y).mp hy
  have hRegions (t : ℝ) :
      Phi t '' (F '' ball (0 : E3) 1) = F '' ball (0 : E3) 1 ∧
      Phi t '' (F '' closedBall (0 : E3) 1) = F '' closedBall (0 : E3) 1 ∧
      Phi t '' S = S ∧ (Phi t).symm '' S = S := by
    refine ⟨hImage _ ?_ t, hImage _ ?_ t, hImage S hSflow t, hImage S hSflow (-t)⟩
    · intro y hy s
      rw [hBall, hRadius]
      exact (hBall y).mp hy
    · intro y hy s
      rw [hClosedBall, hRadius]
      exact (hClosedBall y).mp hy
  have hXon (i : Fin 2) (y : E3) (hy : y ∈ T i) : X y = Xi i y := by
    fin_cases i
    · change Xi 0 y + Xi 1 y = Xi 0 y
      rw [hXiZ 1 y (fun hn => disjoint_left.mp hTdis hy hn), add_zero]
    · change Xi 0 y + Xi 1 y = Xi 1 y
      rw [hXiZ 0 y (fun hp => disjoint_left.mp hTdis hp hy), zero_add]
  have hTflow (i : Fin 2) (y : E3) (hy : y ∈ T i) (t : ℝ) :
      boundedFlow X hK hB y t ∈ T i := by
    obtain ⟨Ki, Bi, hKi, hBi⟩ := compactField_bounds (Xi i) (hXi i).1 (hXi i).2.1
    have hm (s : ℝ) : boundedFlow (Xi i) hKi hBi y s ∈ T i :=
      boundedFlow_mapsTo_set (Xi i) hKi hBi (hXiZ i) s hy
    have hdv (s : ℝ) : HasDerivAt (boundedFlow (Xi i) hKi hBi y)
        (X (boundedFlow (Xi i) hKi hBi y s)) s := by
      rw [hXon i _ (hm s)]
      exact boundedFlow_hasDerivAt (Xi i) hKi hBi y s
    have heq := boundedField_solution_unique X hK hdv
      (boundedFlow_hasDerivAt X hK hB y) (by simp only [boundedFlow_zero])
    rw [← congrFun heq t]
    exact hm t
  have hTimages (i : Fin 2) (t : ℝ) :
      Phi t '' T i = T i ∧ (Phi t).symm '' T i = T i :=
    ⟨hImage (T i) (hTflow i) t, hImage (T i) (hTflow i) (-t)⟩
  have hFixed (t : ℝ) (y : E3)
      (hy : q (sphereDirection (F.symm y)) ≤ 1 / (8 * a ^ 2) ∨
        4 * nu * b ≤ |H y - c| ∨ y ∉ ⋃ i : Fin 2, T i) :
      Phi t y = y ∧ (Phi t).symm y = y := by
    have hz : X y = 0 := by
      apply hXZ y
      intro hc
      rcases hy with hy | hy | hy
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hCsub hc).1
        have hp := hi.2.2
        rw [hQt i] at hp
        exact (not_lt_of_ge hy) hp.2.2
      · exact (not_lt_of_ge hy) (hCsub hc).2
      · exact hy (hCsub hc).1
    exact ⟨boundedFlow_eq_self X hK hB y hz t,
      boundedFlow_eq_self X hK hB y hz (-t)⟩
  have hScale (t : ℝ) (ht : |t| ≤ 2 * (nu * b)) : |t / nu| ≤ 2 * b := by
    rw [abs_div, abs_of_pos hnu, div_le_iff₀ hnu]
    nlinarith only [ht]
  have hScaleBack (h : ℝ) (hh : |h| ≤ 2 * b) : |nu * h| ≤ 2 * (nu * b) := by
    rw [abs_mul, abs_of_pos hnu]
    nlinarith only [mul_le_mul_of_nonneg_left hh hnu.le]
  have hFlowC (y : E3) : Continuous (boundedFlow X hK hB y) :=
    continuous_iff_continuousAt.mpr (fun t => (boundedFlow_hasDerivAt X hK hB y t).continuousAt)
  have hPhysicalDer (k : Fin 4) (R : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (s : ℝ) (hs : |s| ≤ zeta) (t : ℝ) (ht : |t| ≤ 2 * (nu * b)) :
      HasDerivAt (fun v : ℝ => F ((1 + s) • Z k (v / nu) R))
        (X (F ((1 + s) • Z k (t / nu) R))) t := by
    have he : nu * (t / nu) = t := by field_simp [hnu.ne']
    simpa only [he] using hDer k R hR (t / nu) s (hScale t ht) hs
  have hTrack0 (k : Fin 4) (R : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (s : ℝ) (hs : |s| ≤ zeta) (t : ℝ) (ht : |t| ≤ 2 * (nu * b)) :
      boundedFlow X hK hB (F ((1 + s) • Z k 0 R)) t =
        F ((1 + s) • Z k (t / nu) R) := by
    have hc : ContinuousOn (fun v : ℝ => F ((1 + s) • Z k (v / nu) R))
        (Icc (-(2 * (nu * b))) (2 * (nu * b))) := fun v hv =>
      (hPhysicalDer k R hR s hs v (abs_le.mpr hv)).continuousAt.continuousWithinAt
    have hu := ODE_solution_unique_of_mem_Icc (v := fun _ : ℝ => X) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-(2 * (nu * b))) (2 * (nu * b)) from
        ⟨by linarith only [hdelta], by linarith only [hdelta]⟩)
      (hFlowC (F ((1 + s) • Z k 0 R))).continuousOn
      (fun v _ => boundedFlow_hasDerivAt X hK hB (F ((1 + s) • Z k 0 R)) v)
      (fun _ _ => mem_univ _) hc
      (fun v hv => hPhysicalDer k R hR s hs v (abs_le.mpr ⟨hv.1.le, hv.2.le⟩))
      (fun _ _ => mem_univ _) (by simp only [boundedFlow_zero, zero_div])
    exact hu (abs_le.mp ht)
  have hTracks (k : Fin 4) (R : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (h0 h1 s : ℝ) (h0b : |h0| ≤ 2 * b) (h1b : |h1| ≤ 2 * b) (hs : |s| ≤ zeta) :
      Phi (nu * (h1 - h0)) (F ((1 + s) • Z k h0 R)) =
          F ((1 + s) • Z k h1 R) ∧
        (Phi (nu * (h1 - h0))).symm (F ((1 + s) • Z k h1 R)) =
          F ((1 + s) • Z k h0 R) := by
    have hh (h : ℝ) (hb' : |h| ≤ 2 * b) :
        boundedFlow X hK hB (F ((1 + s) • Z k 0 R)) (nu * h) =
          F ((1 + s) • Z k h R) := by
      have he : nu * h / nu = h := by field_simp [hnu.ne']
      simpa only [he] using hTrack0 k R hR s hs (nu * h) (hScaleBack h hb')
    have hf : Phi (nu * (h1 - h0)) (F ((1 + s) • Z k h0 R)) =
        F ((1 + s) • Z k h1 R) := by
      rw [hPhi, ← hh h0 h0b, ← boundedFlow_add]
      rw [show nu * h0 + nu * (h1 - h0) = nu * h1 by ring]
      exact hh h1 h1b
    exact ⟨hf, by rw [← hf, (Phi (nu * (h1 - h0))).symm_apply_apply]⟩
  have hThree (h : ℝ) (hh : |h| ≤ 2 * b) : |h| ≤ 3 * b := by
    linarith only [hh, hb]
  have hI (h : ℝ) (hh : |h| ≤ 3 * b) : h ∈ Ioo (-4 * b) (4 * b) :=
    ⟨by linarith only [(abs_le.mp hh).1, hb],
      by linarith only [(abs_le.mp hh).2, hb]⟩
  have hQCompare (i : Fin 2) (h t : ℝ) (hz : (t, h) ∈ (Q i).source) :
      (2 / a ^ 2 ≤ q (Q i (t, h)) ↔ t ∈ Icc (0 : ℝ) 1) ∧
      (2 / a ^ 2 < q (Q i (t, h)) ↔ t ∈ Ioo (0 : ℝ) 1) := by
    apply hCompare i h t
    have hsrc := (hQall i).1
    change (Q i).source = _ at hsrc
    rwa [← hsrc]
  let kl : Fin 2 → Fin 4 := ![0, 2]
  let kr : Fin 2 → Fin 4 := ![1, 3]
  have hEndpoints (i : Fin 2) (h : ℝ) (hh : |h| ≤ 3 * b) :
      j (Q i (0, h)) = F (Z (kl i) h 1) ∧
      j (Q i (1, h)) = F (Z (kr i) h 1) := by
    have he := hQends i h (hI h hh) 1 (by norm_num)
    have hl := congrArg (fun p : E3 => F p) he.2.2.1
    have hr := congrArg (fun p : E3 => F p) he.2.2.2
    constructor
    · fin_cases i <;> simpa [j, Z, eps, sx, sy, kl] using hl
    · fin_cases i <;> simpa [j, Z, eps, sx, sy, kr] using hr
  let Aext : Set E3 := j '' {p : UnitTwoSphere | 2 / a ^ 2 ≤ q p}
  let Cwall : Set E3 := j '' {p : UnitTwoSphere | q p ≤ 2 / a ^ 2}
  let Utrack : Set E3 := {y : E3 | |H y - c| < 3 * (nu * b)} \ Cwall
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hAc : IsClosed Aext := ((isClosed_le continuous_const hq).isCompact.image hj).isClosed
  have hCc : IsClosed Cwall := ((isClosed_le hq continuous_const).isCompact.image hj).isClosed
  have hU : IsOpen Utrack :=
    (isOpen_lt (H.continuous.sub continuous_const).abs continuous_const).sdiff hCc
  have hAS : Aext ⊆ S := by rintro y ⟨p, _hp, rfl⟩; exact ⟨p, rfl⟩
  have hSC : S \ Cwall ⊆ Aext := by
    rintro y ⟨⟨p, rfl⟩, hp⟩
    have hqgt : 2 / a ^ 2 < q p := not_le.mp (fun hh => hp ⟨p, hh, rfl⟩)
    exact ⟨p, hqgt.le, rfl⟩
  have hUnitTrack (y : E3) (hy : y ∈ S ∩ Utrack) : H (X y) = 1 := by
    obtain ⟨p, rfl⟩ := hy.1
    have hpq : 2 / a ^ 2 < q p := not_le.mp (fun hh => hy.2.2 ⟨p, hh, rfl⟩)
    have hpheight := hy.2.1
    change |H (j p) - c| < 3 * (nu * b) at hpheight
    rw [hJH, add_sub_cancel_left, abs_mul, abs_of_pos hnu] at hpheight
    apply hUnit p ?_ hpq.le
    nlinarith only [hpheight, hnu]
  have hSafe (y : E3) (hy : y ∈ Aext \ Cwall) (hh : |H y - c| ≤ 2 * (nu * b)) :
      y ∈ Utrack := by
    change |H y - c| < 3 * (nu * b) ∧ y ∉ Cwall
    exact ⟨by linarith only [hh, hdelta], hy.2⟩
  have hLevel (h : ℝ) : E h = {y : E3 | y ∈ Aext ∧ H y = c + nu * h} := by
    ext y
    constructor
    · rintro ⟨p, ⟨hp, hqp⟩, rfl⟩
      exact ⟨⟨p, hqp, rfl⟩, by rw [hJH, hp]⟩
    · rintro ⟨⟨p, hqp, rfl⟩, hp⟩
      refine ⟨p, ⟨?_, hqp⟩, rfl⟩
      rw [hJH] at hp
      exact (mul_left_cancel₀ hnu.ne') (add_left_cancel hp)
  have hEndWall (i : Fin 2) (h e : ℝ) (hh : |h| ≤ 3 * b) (he : e = 0 ∨ e = 1) :
      j (Q i (e, h)) ∈ Aext ∩ Cwall ∧ H (j (Q i (e, h))) = c + nu * h := by
    have hei : e ∈ Icc (0 : ℝ) 1 := by rcases he with rfl | rfl <;> norm_num
    have hsrc := (hCover h hh).1 i e hei
    have hcmp := hQCompare i h e hsrc
    have hge : 2 / a ^ 2 ≤ q (Q i (e, h)) := hcmp.1.mpr hei
    have hle : q (Q i (e, h)) ≤ 2 / a ^ 2 := by
      apply le_of_not_gt
      intro hg
      have hei' := hcmp.2.mp hg
      rcases he with rfl | rfl <;> simp only [mem_Ioo] at hei' <;> linarith
    exact ⟨⟨⟨Q i (e, h), hge, rfl⟩, ⟨Q i (e, h), hle, rfl⟩⟩,
      by rw [hJH, hQH i _ hsrc]⟩
  have hWallNative (h : ℝ) (hh : |h| ≤ 2 * b) :
      {y : E3 | y ∈ Aext ∩ Cwall ∧ H y = c + nu * h} =
        range (fun k : Fin 4 => F (Z k h 1)) := by
    ext y
    constructor
    · rintro ⟨⟨hyA, hyC⟩, hyH⟩
      have hyE : y ∈ E h := (hLevel h).symm ▸ ⟨hyA, hyH⟩
      have heq := (hCover h (hThree h hh)).2.2.1
      rw [heq] at hyE
      have hport (i : Fin 2) (hi : y ∈ Ei i h) :
          y ∈ range (fun k : Fin 4 => F (Z k h 1)) := by
        rw [(hCover h (hThree h hh)).2.1 i] at hi
        obtain ⟨t, ht, hty⟩ := hi
        have hz := (hCover h (hThree h hh)).1 i t ht
        have hle : q (Q i (t, h)) ≤ 2 / a ^ 2 := by
          obtain ⟨p, hp, hpy⟩ := hyC
          have hpq := hji (hty.trans hpy.symm)
          rw [hpq]
          exact hp
        have hnot : ¬ t ∈ Ioo (0 : ℝ) 1 := fun hm =>
          (not_lt_of_ge hle) ((hQCompare i h t hz).2.mpr hm)
        have he : t = 0 ∨ t = 1 := by
          by_cases ht0 : t = 0
          · exact Or.inl ht0
          · exact Or.inr (le_antisymm ht.2 (not_lt.mp (fun ht1 =>
              hnot ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht1⟩)))
        rcases he with rfl | rfl
        · exact ⟨kl i, ((hEndpoints i h (hThree h hh)).1).symm.trans hty⟩
        · exact ⟨kr i, ((hEndpoints i h (hThree h hh)).2).symm.trans hty⟩
      exact hyE.elim (hport 0) (hport 1)
    · rintro ⟨k, rfl⟩
      change F (Z k h 1) ∈ Aext ∩ Cwall ∧ H (F (Z k h 1)) = c + nu * h
      have h0 := hEndWall 0 h 0 (hThree h hh) (Or.inl rfl)
      have h1 := hEndWall 0 h 1 (hThree h hh) (Or.inr rfl)
      have h2 := hEndWall 1 h 0 (hThree h hh) (Or.inl rfl)
      have h3 := hEndWall 1 h 1 (hThree h hh) (Or.inr rfl)
      rw [(hEndpoints 0 h (hThree h hh)).1] at h0
      rw [(hEndpoints 0 h (hThree h hh)).2] at h1
      rw [(hEndpoints 1 h (hThree h hh)).1] at h2
      rw [(hEndpoints 1 h (hThree h hh)).2] at h3
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  let wall : Fin 4 → ℝ → E3 := fun k t => F (Z k (t / nu) 1)
  have hWall (t : ℝ) (ht : |t| ≤ 2 * (nu * b)) :
      {y : E3 | y ∈ Aext ∩ Cwall ∧ H y = c + t} = range (fun k => wall k t) := by
    have he : nu * (t / nu) = t := by field_simp [hnu.ne']
    simpa only [he, wall] using hWallNative (t / nu) (hScale t ht)
  have hWallFlow (k : Fin 4) (s t : ℝ)
      (hs : |s| ≤ 2 * (nu * b)) (ht : |t| ≤ 2 * (nu * b)) :
      boundedFlow X hK hB (wall k s) (t - s) = wall k t := by
    have hh := (hTracks k 1 (by norm_num) (s / nu) (t / nu) 0
      (hScale s hs) (hScale t ht) (by simpa only [abs_zero] using hzeta.le)).1
    have he : nu * (t / nu - s / nu) = t - s := by field_simp [hnu.ne']
    simpa only [he, hPhi, zero_add, add_zero, one_smul, wall] using hh
  have hBarrier := boundedFlow_exterior_level_images X hK hB H S Cwall Aext Utrack
    hAc hCc hU hAS hSC c (nu * b) hSflow hUnitTrack hSafe wall hWall hWallFlow
  have hEflow (h0 h1 : ℝ) (h0b : |h0| ≤ 2 * b) (h1b : |h1| ≤ 2 * b) :
      Phi (nu * (h1 - h0)) '' E h0 = E h1 ∧
      (Phi (nu * (h1 - h0))).symm '' E h1 = E h0 := by
    have hh := hBarrier (nu * h0) (nu * h1) (hScaleBack h0 h0b) (hScaleBack h1 h1b)
    have he : nu * h1 - nu * h0 = nu * (h1 - h0) := by ring
    change (fun y => boundedFlow X hK hB y (nu * (h1 - h0))) '' E h0 = E h1 ∧
      (fun y => boundedFlow X hK hB y (-(nu * (h1 - h0)))) '' E h1 = E h0
    simpa only [he, ← hLevel h0, ← hLevel h1] using hh
  have hEiInter (i : Fin 2) (h : ℝ) (hh : |h| ≤ 3 * b) : Ei i h = E h ∩ T i := by
    ext y
    constructor
    · rintro ⟨p, ⟨hps, hpf, hpq⟩, rfl⟩
      refine ⟨⟨p, ⟨hpf, hpq⟩, rfl⟩, ?_⟩
      change 1 / 2 < ‖F.symm (j p)‖ ∧ ‖F.symm (j p)‖ < 3 / 2 ∧
        sphereDirection (F.symm (j p)) ∈ (Q i).target
      rw [show F.symm (j p) = (p : E3) from F.symm_apply_apply _]
      rw [norm_eq_of_mem_sphere p]
      refine ⟨by norm_num, by norm_num, ?_⟩
      rw [show sphereDirection (p : E3) = p by
        simpa only [one_smul] using sphereDirection_smul p (by norm_num : (0 : ℝ) < 1)]
      rw [hQt i]
      refine ⟨hpf.symm ▸ hI h hh, hps, lt_of_lt_of_le ?_ hpq⟩
      have he := div_lt_div_of_pos_right (by norm_num : (1 / 8 : ℝ) < 2) (sq_pos_of_pos ha)
      simpa only [div_div] using he
    · rintro ⟨⟨p, ⟨hpf, hpq⟩, rfl⟩, hpT⟩
      have hp := hpT.2.2
      rw [hdir, hQt i] at hp
      exact ⟨p, ⟨hp.2.1, hpf, hpq⟩, rfl⟩
  refine ⟨zeta, X, K, B, hK, hB, hX, hcX, C, hzeta, hzetaSmall, hC, hXs,
    hCsub, hPhiSmooth, hPhiISmooth, ?_, ?_, ?_, ?_, hRegions, hTimages,
    hFixed, hUnit, hCover, hZ, hDer, hTracks, ?_⟩
  · intro y
    exact boundedFlow_zero X hK hB y
  · intro t y
    exact ⟨hPhi t y, hPhii t y⟩
  · intro t
    exact ⟨hSupport t, hSupport (-t)⟩
  · intro t y
    exact ⟨hRadius y t, hRadius y (-t)⟩
  · intro h0 h1 h0b h1b
    obtain ⟨hf, hi⟩ := hEflow h0 h1 h0b h1b
    refine ⟨?_, hf, hi⟩
    intro i
    change Phi (nu * (h1 - h0)) '' Ei i h0 = Ei i h1 ∧
      (Phi (nu * (h1 - h0))).symm '' Ei i h1 = Ei i h0
    constructor
    · rw [hEiInter i h0 (hThree h0 h0b),
        image_inter (f := Phi (nu * (h1 - h0))) (Phi _).injective,
        hf, (hTimages i _).1, ← hEiInter i h1 (hThree h1 h1b)]
    · rw [hEiInter i h1 (hThree h1 h1b),
        image_inter (f := (Phi (nu * (h1 - h0))).symm) (Phi _).symm.injective,
        hi, (hTimages i _).2, ← hEiInter i h0 (hThree h0 h0b)]

end PoincareConjecture.M25.Topology3D
