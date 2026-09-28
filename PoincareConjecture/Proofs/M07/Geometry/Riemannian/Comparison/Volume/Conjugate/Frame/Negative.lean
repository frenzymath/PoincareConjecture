import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateFrame

open ConnectionAlongCurve ConnectionVariation CoordinateExponential
open Poincare.ODE.Jacobi

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1000000 in
theorem exists_negative_intrinsic_split
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b c : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ0 : J 0 = 0) (hJc : J c = 0)
    (hDJ0 : manifoldCovDerivAlong g q J 1 0 ≠ 0) :
    ∃ V₀ V₁ : (t : ℝ) → TangentSpace (𝓡 n) (q t),
      (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V₀) t) ∧
      (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V₁) t) ∧
      V₀ 0 = 0 ∧ V₁ 1 = 0 ∧ V₀ c = V₁ c ∧
      (∫ t in (0 : ℝ)..c, ConjugateVariation.intrinsicIndexIntegrand g D q V₀ t) +
        (∫ t in c..1, ConjugateVariation.intrinsicIndexIntegrand g D q V₁ t) < 0 := by
  classical
  have hab : a < b := ha.trans (zero_lt_one.trans hb)
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo a b :=
    fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have h01' : Icc (0 : ℝ) 1 ⊆ Icc a b := h01.trans Ioo_subset_Icc_self
  have hqt := fun t ht => hq.contMDiffAt (hI.mem_nhds (show t ∈ I from ht))
  obtain ⟨P, hi, hP, hp⟩ := exists_orthonormal_parallel_transport g hab hI hq hsub
  let A := coefficient g q P
  let R := fun t => if t ∈ Ioo a b then A t else 0
  let y := fun t => (P t).inverse (J t)
  let v := fun t => (P t).inverse (manifoldCovDerivAlong g q J 1 t)
  have hRt (t : ℝ) (ht : t ∈ Ioo a b) : R t = A t := if_pos ht
  have hAt (t : ℝ) (ht : t ∈ Icc a b) (u : EuclideanSpace ℝ (Fin n)) :
      A t u = (P t).inverse (D.curvature (q t) (P t u)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) :=
    chartCoefficient_apply D P (mem_extChartAt_source _) (hqt t (hsub ht)) u
  have hRc : ContDiffOn ℝ ∞ R (Ioo a b) := by
    intro t ht
    have hs := contDiffAt_coefficient D hI hq (hsub (Ioo_subset_Icc_self ht))
      (hi t (Ioo_subset_Icc_self ht)) (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
    have heq : R =ᶠ[𝓝 t] A := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hRt s hs
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt
  have hRs : ∀ t, ∀ u w : EuclideanSpace ℝ (Fin n),
      inner ℝ (R t u) w = inner ℝ u (R t w) := by
    intro t u w
    by_cases ht : t ∈ Ioo a b
    · have ht' := Ioo_subset_Icc_self ht
      rw [hRt t ht, ← hp t ht', ← hp t ht', hAt t ht', hAt t ht',
        (hi t ht').self_apply_inverse, (hi t ht').self_apply_inverse]
      exact curvature_jacobi_symm D _ _ _ _
    · simp only [R, if_neg ht, zero_apply, inner_zero_left, inner_zero_right]
  have hyd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt y (v t) t :=
    inverse_manifold_parallel_hasDerivAt g hab ht hi (hqt t (hsub ht))
      (hP t ht) ((hJ t (hsub ht)).differentiableAt (by simp))
  have hys : ContDiffOn ℝ ∞ y (Ioo a b) := by
    intro t ht
    exact (contDiffAt_inverse_frame_field (hi t (Ioo_subset_Icc_self ht))
      (hqt t (hsub (Ioo_subset_Icc_self ht)))
      (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
      (hJ t (hsub (Ioo_subset_Icc_self ht)))).contDiffWithinAt
  have hsol : IsJacobiSolOn R 0 1 y v := by
    constructor
    · exact fun t ht => (hyd t (h01' ht)).hasDerivWithinAt
    · intro t ht
      have hDJ := contDiffAt_chartField_covDeriv g hI hq hJ
        (hsub (h01' ht)) (mem_extChartAt_source _)
      have hd := inverse_manifold_parallel_hasDerivAt g hab (h01' ht) hi
        (hqt t (hsub (h01' ht))) (hP t (h01' ht))
        (hDJ.differentiableAt (by simp))
      rw [hjac t ht, map_neg] at hd
      have heq := hAt t (h01' ht) ((P t).inverse (J t))
      rw [(hi t (h01' ht)).self_apply_inverse] at heq
      rw [← heq, ← hRt t (h01 ht)] at hd
      exact hd.hasDerivWithinAt
  have hy0 : y 0 = 0 := by simp [y, hJ0]
  have hyc : y c = 0 := by simp [y, hJc]
  have hyne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : HasDerivWithinAt y (0 : EuclideanSpace ℝ (Fin n)) (Icc 0 1) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Icc 0 1) (0 : EuclideanSpace ℝ (Fin n))).congr
        (fun t ht => h t ht) hy0
    have hv0 : v 0 = 0 :=
      ((hsol.hasDerivWithinAt_fst 0 ⟨le_rfl, zero_le_one⟩).derivWithin
        (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩)).symm.trans
      (hzero.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩))
    apply hDJ0
    have hv0' := congrArg (P 0) hv0
    simpa only [v, (hi 0 (h01' ⟨le_rfl, zero_le_one⟩)).self_apply_inverse,
      map_zero] using hv0'
  obtain ⟨s, hs⟩ := hsol.exists_split_neg hc (hRc.continuousOn.mono h01) hRs hy0 hyc hyne
  let Z := indexTestField (v c)
  let DZ := indexTestDeriv (v c)
  let W₀ := y + s • Z
  let W₁ := s • Z
  have hZd : ∀ t, HasDerivAt Z (DZ t) t := indexTestField_deriv (v c)
  have hZs : ContDiff ℝ ∞ Z := testField_smooth (v c)
  have hW₀s : ContDiffOn ℝ ∞ W₀ (Ioo a b) :=
    hys.add (hZs.const_smul s).contDiffOn
  have hW₁s : ContDiff ℝ ∞ W₁ := hZs.const_smul s
  have hW₀d (t : ℝ) (ht : t ∈ Icc a b) :
      deriv W₀ t = (v + s • DZ) t := by
    simpa only [Pi.add_apply, Pi.smul_apply] using
      ((hyd t ht).add ((hZd t).const_smul s)).deriv
  have hW₁d (t : ℝ) : deriv W₁ t = (s • DZ) t := by
    simpa only [Pi.smul_apply] using ((hZd t).const_smul s).deriv
  let V₀ : (t : ℝ) → TangentSpace (𝓡 n) (q t) := fun t => P t (W₀ t)
  let V₁ : (t : ℝ) → TangentSpace (𝓡 n) (q t) := fun t => P t (W₁ t)
  have hV₀s : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V₀) t := by
    intro t ht
    exact contDiffAt_frame_field (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
      (hW₀s.contDiffAt (isOpen_Ioo.mem_nhds ht))
  have hV₁s : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V₁) t := by
    intro t ht
    exact contDiffAt_frame_field (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
      hW₁s.contDiffAt
  refine ⟨V₀, V₁, hV₀s, hV₁s, ?_, ?_, ?_, ?_⟩
  · simp [V₀, W₀, Z, indexTestField, indexTestFieldTo, hy0]
  · simp [V₁, W₁, Z, indexTestField, indexTestFieldTo]
  · simp [V₀, V₁, W₀, W₁, hyc]
  · have e₀ : (∫ t in (0 : ℝ)..c,
        ConjugateVariation.intrinsicIndexIntegrand g D q V₀ t) =
        indexForm R 0 c W₀ (v + s • DZ) W₀ (v + s • DZ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hc.1.le] at ht
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hc.2.le⟩
      rw [indexIntegrand_frame_field D (h01 ht01) hi
        (hqt t (hsub (h01' ht01))) (hP t (h01' ht01)) (hp t (h01' ht01))
        (hW₀s.contDiffAt (isOpen_Ioo.mem_nhds (h01 ht01)))]
      simp only [indexIntegrand, hW₀d t (h01' ht01), hRt t (h01 ht01), A]
    have e₁ : (∫ t in c..(1 : ℝ),
        ConjugateVariation.intrinsicIndexIntegrand g D q V₁ t) =
        indexForm R c 1 W₁ (s • DZ) W₁ (s • DZ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hc.2.le] at ht
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le.trans ht.1, ht.2⟩
      rw [indexIntegrand_frame_field D (h01 ht01) hi
        (hqt t (hsub (h01' ht01))) (hP t (h01' ht01)) (hp t (h01' ht01))
        hW₁s.contDiffAt]
      simp only [indexIntegrand, hW₁d t, hRt t (h01 ht01), A]
    rw [e₀, e₁]
    exact hs

end PoincareConjecture.ConjugateFrame
