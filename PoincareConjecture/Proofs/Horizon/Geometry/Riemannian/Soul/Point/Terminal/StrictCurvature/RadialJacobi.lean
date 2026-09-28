import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.RadialHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.IndexComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Conjugate

open ConnectionAlongCurve ConnectionVariation CoordinateExponential ConjugateFrame
open ConjugateVariation Poincare.ODE.Jacobi

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1000000 in

theorem exists_parallel_field_jacobi_inner_le_sub_curvature_integral_of_minimizing
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b C : ℝ}
    (ha : a < 0) (hb : 1 < b)
    (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ0 : J 0 = 0) (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hmin : g.edist (q 0) (q 1) = ENNReal.ofReal C) :
    ∃ Z : (t : ℝ) → TangentSpace (𝓡 n) (q t),
      (∀ t ∈ Icc a b, ContDiffAt ℝ ∞ (chartField q (q t) Z) t) ∧
      (∀ t ∈ Icc a b, manifoldCovDerivAlong g q Z 1 t = 0) ∧
      Z 1 = J 1 ∧
      (∀ t ∈ Icc a b, g.tangentNorm (q t) (Z t) = g.tangentNorm (q 1) (J 1)) ∧
      ContinuousOn (fun t => D.curvatureTensor (q t) (t • Z t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) (Icc 0 1) ∧
      g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) ≤
        g.inner (q 1) (J 1) (J 1) -
          ∫ t in (0 : ℝ)..1, D.curvatureTensor (q t) (t • Z t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
  classical
  have hab : a < b := ha.trans (zero_lt_one.trans hb)
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo a b :=
    fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have h01' : Icc (0 : ℝ) 1 ⊆ Icc a b := h01.trans Ioo_subset_Icc_self
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
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
  have hRc : ContinuousOn R (Icc 0 1) := by
    intro t ht
    have hs := contDiffAt_coefficient D hI hq (hsub (h01' ht))
      (hi t (h01' ht)) (fun u => (hP t (h01' ht) u).1)
    have heq : R =ᶠ[𝓝 t] A := by
      filter_upwards [isOpen_Ioo.mem_nhds (h01 ht)] with s hs
      exact hRt s hs
    exact (hs.congr_of_eventuallyEq heq).continuousAt.continuousWithinAt
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
  let W : ℝ → EuclideanSpace ℝ (Fin n) := y - fun t => t • y 1
  let W' : ℝ → EuclideanSpace ℝ (Fin n) := v - fun _ => y 1
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun t => P t (W t)
  have hWs : ContDiffOn ℝ ∞ W (Ioo a b) :=
    hys.sub ((contDiff_id.smul contDiff_const).contDiffOn)
  have hWd (t : ℝ) (ht : t ∈ Icc a b) : deriv W t = W' t := by
    simpa only [W, W', Pi.sub_apply, id_eq, one_smul] using
      ((hyd t ht).sub ((hasDerivAt_id t).smul_const (y 1))).deriv
  have hVs : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V) t := by
    intro t ht
    exact contDiffAt_frame_field (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
      (hWs.contDiffAt (isOpen_Ioo.mem_nhds ht))
  have hindex := Realization.index_nonneg_of_minimizing g D
    (a := 0) (c := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    isOpen_Ioo h01 (fun t ht => hgeo t (hsub (Ioo_subset_Icc_self ht)))
    hVs hVs rfl (by simp [V, W, hy0]) (by simp [V, W]) hC hspeed
    (by simpa only [sub_zero, one_mul] using hmin)
  have heq (t : ℝ) (ht : t ∈ Icc 0 1) :
      intrinsicIndexIntegrand g D q V t = indexIntegrand R W W' W W' t := by
    rw [indexIntegrand_frame_field D (h01 ht) hi (hqt t (hsub (h01' ht)))
      (hP t (h01' ht)) (hp t (h01' ht))
      (hWs.contDiffAt (isOpen_Ioo.mem_nhds (h01 ht)))]
    simp only [indexIntegrand, hWd t (h01' ht), hRt t (h01 ht), A]
  have hWc : ContinuousOn W (Icc 0 1) := hWs.continuousOn.mono h01
  have hWc' : ContinuousOn W' (Icc 0 1) := hsol.continuousOn_snd.sub continuousOn_const
  have hIc : ContinuousOn (intrinsicIndexIntegrand g D q V) (Icc 0 1) :=
    (contOn_indexIntegrand hRc hWc hWc' hWc hWc').congr
      (fun t ht => heq t ht)
  have hIi : IntervalIntegrable (intrinsicIndexIntegrand g D q V) volume 0 1 :=
    hIc.intervalIntegrable_of_Icc zero_le_one
  have hhalf₀ : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf₁ : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hIi.mono_set (by
      simpa only [uIcc_of_le hhalf₀, uIcc_of_le zero_le_one] using
        Icc_subset_Icc le_rfl hhalf₁))
    (hIi.mono_set (by
      simpa only [uIcc_of_le hhalf₁, uIcc_of_le zero_le_one] using
        Icc_subset_Icc hhalf₀ le_rfl))] at hindex
  have hidx : 0 ≤ indexForm R 0 1 W W' W W' := by
    convert hindex using 1
    exact intervalIntegral.integral_congr fun t ht =>
      (heq t (by simpa only [uIcc_of_le zero_le_one] using ht)).symm
  have ht1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hvP : P 1 (v 1) = manifoldCovDerivAlong g q J 1 1 := by
    simp only [v]
    exact (hi 1 (h01' ht1)).self_apply_inverse _
  have hyP : P 1 (y 1) = J 1 := by
    simp only [y]
    exact (hi 1 (h01' ht1)).self_apply_inverse _
  let Z : (t : ℝ) → TangentSpace (𝓡 n) (q t) := fun t => P t (y 1)
  have hcurvature (t : ℝ) (ht : t ∈ Icc 0 1) :
      D.curvatureTensor (q t) (t • Z t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (t • Z t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) =
      inner ℝ (R t (t • y 1)) (t • y 1) := by
    rw [hRt t (h01 ht), ← hp t (h01' ht), hAt t (h01' ht),
      (hi t (h01' ht)).self_apply_inverse]
    simp only [LeviCivitaData.curvatureTensor, Z, map_smul]
  have hz : ContinuousOn (fun t : ℝ => t • y 1) (Icc 0 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have hcontinuous : ContinuousOn (fun t => D.curvatureTensor (q t) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) (Icc 0 1) :=
    ((hRc.clm_apply hz).inner hz).congr hcurvature
  have hintegral : (∫ t in (0 : ℝ)..1, D.curvatureTensor (q t) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) =
      ∫ t in (0 : ℝ)..1, inner ℝ (R t (t • y 1)) (t • y 1) :=
    intervalIntegral.integral_congr fun t ht =>
      hcurvature t (by simpa only [uIcc_of_le zero_le_one] using ht)
  refine ⟨Z, fun t ht => (hP t ht (y 1)).1,
    fun t ht => (hP t ht (y 1)).2, hyP, ?_, hcontinuous, ?_⟩
  · intro t ht
    change Real.sqrt (g.inner (q t) (P t (y 1)) (P t (y 1))) =
      Real.sqrt (g.inner (q 1) (J 1) (J 1))
    rw [hp t ht, ← hyP, hp 1 (h01' ht1)]
  · have hbound := hsol.inner_endpoint_le_affine_sub_curvature_integral hRc hRs hy0 hidx
    calc
      g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) =
          inner ℝ (v 1) (y 1) := by rw [← hvP, ← hyP, hp 1 (h01' ht1)]
      _ ≤ inner ℝ (y 1) (y 1) -
          ∫ t in (0 : ℝ)..1, inner ℝ (R t (t • y 1)) (t • y 1) := hbound
      _ = g.inner (q 1) (J 1) (J 1) -
          ∫ t in (0 : ℝ)..1, D.curvatureTensor (q t) (t • Z t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
        rw [hintegral, ← hyP, hp 1 (h01' ht1)]

theorem jacobi_inner_lt_of_minimizing_of_curvature_pos
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b C : ℝ}
    (ha : a < 0) (hb : 1 < b)
    (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ0 : J 0 = 0) (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hmin : g.edist (q 0) (q 1) = ENNReal.ofReal C)
    (hsec : D.NonnegativeSectionalCurvature)
    (hcurv : 0 < D.curvatureTensor (q 1) (J 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1) (J 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) :
    g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) <
      g.inner (q 1) (J 1) (J 1) := by
  obtain ⟨Z, _, _, hZ1, _, hcontinuous, hbound⟩ :=
    exists_parallel_field_jacobi_inner_le_sub_curvature_integral_of_minimizing
      D ha hb hI hgeo hsub hJ hjac hJ0 hC hspeed hmin
  have hpositive : 0 < ∫ t in (0 : ℝ)..1, D.curvatureTensor (q t) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (t • Z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    apply intervalIntegral.integral_pos zero_lt_one hcontinuous
    · exact fun t _ => hsec (q t) (t • Z t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa only [one_smul, hZ1] using hcurv⟩
  linarith

end PoincareConjecture.Conjugate
