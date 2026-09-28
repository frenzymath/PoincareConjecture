import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Operator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold
import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.LowerBound
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ParallelFrame


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ManifoldJacobi

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_multilinear_curvatureTensor
    (D : LeviCivitaData g) (x : M) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v := by
  let A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ :=
    { toFun := fun v => D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)
      map_update_add' := by
        classical
        intro _ v i a b
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_first x a b (v 1) (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_second x (v 0) a b (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_third x (v 0) (v 1) a (v 3) b
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_last x (v 0) (v 1) (v 2) a b
      map_update_smul' := by
        classical
        intro _ v i c a
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_first x c a (v 1) (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_second x c (v 0) a (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_third x c (v 0) (v 1) a (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_last x c (v 0) (v 1) (v 2) a }
  exact ⟨A, by intro v; rfl⟩



theorem curvature_norm_le
    (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    g.tangentNorm x (D.curvature x u v w) ≤ D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let R : TangentSpace (𝓡 n) x := D.curvature x u v w
  have hnorm (q : TangentSpace (𝓡 n) x) : g.tangentNorm x q = ‖q‖ := by
    change Real.sqrt (inner ℝ q q) = ‖q‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)]
  obtain ⟨A, hA⟩ := exists_multilinear_curvatureTensor D x
  have h := D.abs_curvatureTensor_le_of_multilinear x A hA u v R w
  have hself : |D.curvatureTensor x u v R w| = ‖R‖ ^ 2 := by
    change |inner ℝ R R| = ‖R‖ ^ 2
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  rw [hself, hnorm R] at h
  rw [hnorm]
  change ‖R‖ ≤ _
  by_cases hR : ‖R‖ = 0
  · rw [hR]
    unfold RiemannianMetric.tangentNorm LeviCivitaData.curvatureTensorNorm
    positivity
  · have hpos : 0 < ‖R‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hR)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [h]






theorem transported_jacobi_two_sided_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q : ℝ → M} {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    {y v : ℝ → E} {R : ℝ → E →L[ℝ] E} {b C : ℝ}
    (hsol : Poincare.ODE.Jacobi.IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0)
    (hynorm : ∀ s ∈ Icc 0 b, ‖y s‖ = g.tangentNorm (q s) (J s))
    (hvnorm : ‖v 0‖ = g.tangentNorm (q 0) (J 0)) {t : ℝ}
    (ht : t ∈ Icc 0 b)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 ≤ 3) :
    t * g.tangentNorm (q 0) (J 0) / 2 ≤ g.tangentNorm (q t) (J t) ∧
      g.tangentNorm (q t) (J t) ≤ 3 * t * g.tangentNorm (q 0) (J 0) / 2 := by
  have hrem := Poincare.ODE.Jacobi.norm_sub_linear_le hsol hR hC hy0 ht
  have hlower := Poincare.ODE.Jacobi.half_norm_lower_bound
    hsol hR hC hy0 ht hsmall
  have htri : ‖y t‖ ≤ ‖t • v 0‖ + ‖y t - t • v 0‖ := by
    calc
      ‖y t‖ = ‖(y t - t • v 0) + t • v 0‖ := by congr 1; abel
      _ ≤ ‖y t - t • v 0‖ + ‖t • v 0‖ := norm_add_le _ _
      _ = ‖t • v 0‖ + ‖y t - t • v 0‖ := add_comm _ _
  have ht0 : 0 ≤ t := ht.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at htri
  have hnonneg : 0 ≤ ‖v 0‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  have hupper : ‖y t‖ ≤ 3 * t * ‖v 0‖ / 2 := by
    nlinarith [hrem, htri, hmul]
  constructor
  · simpa [hynorm t ht, hvnorm] using hlower
  · simpa [hynorm t ht, hvnorm] using hupper

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

private def chartCoefficient (g : RiemannianMetric n M) (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (a : M) (t : ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
  let Q := L.comp (P t)
  Q.inverse.comp ((jacobiCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
    (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t)).comp Q)

set_option maxHeartbeats 1000000 in
private theorem chartCoefficient_apply (D : LeviCivitaData g)
    {q : ℝ → M}
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {a : M} {t : ℝ} (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) (u : EuclideanSpace ℝ (Fin n)) :
    chartCoefficient g q P a t u = (P t).inverse (D.curvature (q t) (P t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
  have hv : deriv ((extChartAt (𝓡 n) a) ∘ q) t =
      L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    have hd := mfderiv_comp t (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using ha)) (hq.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact congrArg (fun f => f 1) hd
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha))
  have hΓ := (contDiffAt_christoffelBilinear hB
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))).differentiableAt
      (by simp)
  dsimp only [chartCoefficient, ContinuousLinearMap.comp_apply]
  change ((L.comp (P t)).inverse)
    (jacobiCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t) (L (P t u))) = _
  rw [jacobiCurvature_apply hΓ, hv]
  have hcurv := coordinateCurvature_in_chart g D a ha (P t u)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
  change coordinateCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
    (extChartAt (𝓡 n) a (q t)) (L (P t u)) (L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
      (L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) = L (D.curvature (q t) (P t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) at hcurv
  rw [hcurv]
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt ha
  rw [hL.inverse_comp_apply_of_left, hL.inverse_apply_self]

private theorem contDiffAt_chartCoefficient
    {q : ℝ → M}
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {a : M} {t : ℝ} (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hPi : (P t).IsInvertible)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q a (fun s => P s u)) t) :
    ContDiffAt ℝ ∞ (chartCoefficient g q P a) t := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)
  let Q : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => (L s).comp (P s)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply hP
  have hL : (L t).IsInvertible := isInvertible_mfderiv_extChartAt ha
  have hi := ((hL.comp hPi).contDiffAt_map_inverse (n := ∞)).comp t hQ
  have hqc := contDiffAt_chart_curve hq ha
  have hdq : ContDiffAt ℝ ∞ (deriv ((extChartAt (𝓡 n) a) ∘ q)) t :=
    (hqc.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hC := (contDiffAt_jacobiCurvature
    ((g.contDiffOn_chartCoefficients a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha)))
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))).comp t
      (hqc.prodMk hdq)
  exact hi.clm_comp (hC.clm_comp hQ)

set_option maxHeartbeats 1000000 in
private theorem exists_manifold_jacobi_reduction
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {b K c : ℝ}
    (hb : 0 < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hsub : Icc 0 b ⊆ I)
    (hjac : ∀ t ∈ I, manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
      -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hK : ∀ t ∈ Icc 0 b, D.curvatureTensorNorm (q t) ≤ K)
    (hc : ∀ t ∈ Icc 0 b, g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = c) :
    ∃ P A : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc 0 b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc 0 b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
        manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0) ∧
      (∀ t ∈ Icc 0 b, ∀ u v, g.inner (q t) (P t u) (P t v) = g.inner (q 0) u v) ∧
      Poincare.ODE.Jacobi.IsJacobiSolOn A 0 b (fun t => (P t).inverse (J t))
        (fun t => (P t).inverse (manifoldCovDerivAlong g q J 1 t)) ∧
      ContinuousOn A (Icc 0 b) ∧
      ∀ t ∈ Icc 0 b, ∀ u, g.tangentNorm (q 0) (A t u) ≤
        (K * c ^ 2) * g.tangentNorm (q 0) u := by
  obtain ⟨P, hP0, hPi, hP, hpair⟩ := exists_manifold_parallel_transport g hb hI hq hsub
  let A := fun t => chartCoefficient g q P (q t) t
  have hqt := fun t ht => hq.contMDiffAt (hI.mem_nhds (show t ∈ I from ht))
  have hA (t : ℝ) (ht : t ∈ I) (u : EuclideanSpace ℝ (Fin n)) :
      A t u = (P t).inverse (D.curvature (q t) (P t u)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) :=
    chartCoefficient_apply D P (mem_extChartAt_source _) (hqt t ht) u
  refine ⟨P, A, hP0, hPi, hP, hpair, ?_, ?_, ?_⟩
  · constructor
    · intro t ht
      exact (inverse_manifold_parallel_hasDerivAt g hb ht hPi (hqt t (hsub ht))
        (hP t ht) ((hJ t (hsub ht)).differentiableAt (by simp))).hasDerivWithinAt
    · intro t ht
      have hDJ := contDiffAt_chartField_covDeriv g hI hq hJ (hsub ht) (mem_extChartAt_source _)
      have hd := inverse_manifold_parallel_hasDerivAt g hb ht hPi (hqt t (hsub ht))
        (hP t ht) (hDJ.differentiableAt (by simp))
      rw [hjac t (hsub ht), map_neg] at hd
      have heq := hA t (hsub ht) ((P t).inverse (J t))
      rw [(hPi t ht).self_apply_inverse] at heq
      rw [← heq] at hd
      exact hd.hasDerivWithinAt
  · intro t ht
    have hs := contDiffAt_chartCoefficient (g := g) (mem_extChartAt_source _)
      (hqt t (hsub ht)) (hPi t ht) (fun u => (hP t ht u).1)
    have heq : A =ᶠ[𝓝 t] chartCoefficient g q P (q t) := by
      filter_upwards [hI.mem_nhds (hsub ht), (hqt t (hsub ht)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds (mem_extChartAt_source _))]
        with s hsI hs
      apply ContinuousLinearMap.ext
      intro u
      exact (hA s hsI u).trans (chartCoefficient_apply D P hs (hqt s hsI) u).symm
    exact (hs.continuousAt.congr heq.symm).continuousWithinAt
  · intro t ht u
    have hn (w : EuclideanSpace ℝ (Fin n)) :
        g.tangentNorm (q t) (P t w) = g.tangentNorm (q 0) w :=
      congrArg Real.sqrt (hpair t ht w w)
    have hi (w : EuclideanSpace ℝ (Fin n)) :
        g.tangentNorm (q 0) ((P t).inverse w) = g.tangentNorm (q t) w := by
      rw [← hn, (hPi t ht).self_apply_inverse]
    rw [hA t (hsub ht), hi]
    have h := curvature_norm_le D (q t) (P t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
    rw [hn, hc t ht] at h
    calc
      _ ≤ D.curvatureTensorNorm (q t) * g.tangentNorm (q 0) u * c * c := h
      _ = D.curvatureTensorNorm (q t) * c ^ 2 * g.tangentNorm (q 0) u := by ring
      _ ≤ (K * c ^ 2) * g.tangentNorm (q 0) u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK t ht) (sq_nonneg c))
          (Real.sqrt_nonneg _)

set_option maxHeartbeats 1000000 in


theorem manifold_jacobi_estimates
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {b K c : ℝ}
    (hb : 0 < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hsub : Icc 0 b ⊆ I)
    (hjac : ∀ t ∈ I, manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
      -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hK : ∀ t ∈ Icc 0 b, D.curvatureTensorNorm (q t) ≤ K)
    (hc : ∀ t ∈ Icc 0 b, g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = c)
    (hJ0 : J 0 = 0) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ s ∈ Icc 0 b, (P s).IsInvertible) ∧
      (∀ s ∈ Icc 0 b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q s) (fun r => P r u)) s ∧
        manifoldCovDerivAlong g q (fun r => P r u) 1 s = 0) ∧
      (∀ s ∈ Icc 0 b, ∀ u v,
        g.inner (q s) (P s u) (P s v) = g.inner (q 0) u v) ∧
      ∀ t ∈ Icc 0 b,
        g.tangentNorm (q 0)
            ((P t).inverse (J t) - t •
              (show EuclideanSpace ℝ (Fin n) from manifoldCovDerivAlong g q J 1 0)) ≤
          (K * c ^ 2) * Real.exp (max 1 (K * c ^ 2) * b) * t ^ 3 / 6 *
            g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) ∧
        ((K * c ^ 2) * Real.exp (max 1 (K * c ^ 2) * b) * t ^ 2 ≤ 3 →
          t * g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) / 2 ≤
            g.tangentNorm (q t) (J t) ∧
          g.tangentNorm (q t) (J t) ≤
            3 * t * g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) / 2) := by
  obtain ⟨P, A, hP0, hPi, hP, hpair, hsol, hA, hbound⟩ :=
    exists_manifold_jacobi_reduction D hb hI hq hJ hsub hjac hK hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (q 0)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) (q 0)
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (q 0) :=
    (show EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] TangentSpace (𝓡 n) (q 0) from
      LinearEquiv.refl ℝ _).toContinuousLinearEquiv
  let R : ℝ → TangentSpace (𝓡 n) (q 0) →L[ℝ] TangentSpace (𝓡 n) (q 0) :=
    fun s => e.toContinuousLinearMap.comp ((A s).comp e.symm.toContinuousLinearMap)
  let y := fun s => e ((P s).inverse (J s))
  let v := fun s => e ((P s).inverse (manifoldCovDerivAlong g q J 1 s))
  have henorm (u : EuclideanSpace ℝ (Fin n)) : ‖e u‖ = g.tangentNorm (q 0) u := by
    change ‖e u‖ = Real.sqrt (inner ℝ (e u) (e u))
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsol' : Poincare.ODE.Jacobi.IsJacobiSolOn R 0 b y v := by
    constructor
    · intro s hs
      exact e.hasFDerivAt.comp_hasDerivWithinAt s (hsol.hasDerivWithinAt_fst s hs)
    · intro s hs
      simpa only [R, y, v, Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, map_neg] using
        e.hasFDerivAt.comp_hasDerivWithinAt s (hsol.hasDerivWithinAt_snd s hs)
  have hR : ContinuousOn R (Icc 0 b) :=
    continuousOn_const.clm_comp (hA.clm_comp continuousOn_const)
  have hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ K * c ^ 2 := by
    intro s hs
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg ((Real.sqrt_nonneg _).trans (hK s hs)) (sq_nonneg c))
    intro u
    obtain ⟨w, rfl⟩ := e.surjective u
    simpa only [R, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, henorm] using hbound s hs w
  have hy0 : y 0 = 0 := by simp [y, hJ0]
  have hv0 : ‖v 0‖ =
      g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) := by
    change ‖e ((P 0).inverse (manifoldCovDerivAlong g q J 1 0))‖ = _
    rw [hP0, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply, henorm]
  refine ⟨P, hP0, hPi, hP, hpair, ?_⟩
  intro t ht
  have hyt : ‖y t‖ = g.tangentNorm (q t) (J t) := by
    rw [show y t = e ((P t).inverse (J t)) from rfl, henorm]
    have hp := hpair t ht ((P t).inverse (J t)) ((P t).inverse (J t))
    rw [(hPi t ht).self_apply_inverse] at hp
    exact congrArg Real.sqrt hp.symm
  have hrem := Poincare.ODE.Jacobi.norm_sub_linear_le hsol' hR hC hy0 ht
  constructor
  · have heq : y t - t • v 0 =
        e ((P t).inverse (J t) - t •
          (show EuclideanSpace ℝ (Fin n) from manifoldCovDerivAlong g q J 1 0)) := by
      simp only [y, v, hP0, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply,
        map_sub, map_smul]
    rw [heq, henorm, hv0] at hrem
    convert hrem using 1
    ring
  · intro hsmall
    have hlower := Poincare.ODE.Jacobi.half_norm_lower_bound hsol' hR hC hy0 ht hsmall
    have hupper : ‖y t‖ ≤ 3 * t * ‖v 0‖ / 2 := by
      have htri : ‖y t‖ ≤ ‖t • v 0‖ + ‖y t - t • v 0‖ := by
        calc
          ‖y t‖ = ‖(y t - t • v 0) + t • v 0‖ := by congr 1; abel
          _ ≤ ‖y t - t • v 0‖ + ‖t • v 0‖ := norm_add_le _ _
          _ = ‖t • v 0‖ + ‖y t - t • v 0‖ := add_comm _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at htri
      have hnonneg : 0 ≤ ‖v 0‖ := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
      have hmult := mul_le_mul_of_nonneg_right hmul ht.1
      nlinarith only [hrem, htri, hmult]
    simpa only [hyt, hv0] using And.intro hlower hupper

end PoincareConjecture.ManifoldJacobi
