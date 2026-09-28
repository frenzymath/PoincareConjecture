import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle NNReal

namespace PoincareConjecture.LaplacianComparison

open ConnectionAlongCurve ConnectionVariation CoordinateExponential ConjugateFrame
open Poincare.ODE.Jacobi

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1000000 in

theorem jacobi_eq_zero_of_terminal
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b : ℝ}
    (ha : a < 0) (hb : 1 < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ1 : J 1 = 0) (hDJ1 : manifoldCovDerivAlong g q J 1 1 = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      J t = 0 ∧ manifoldCovDerivAlong g q J 1 t = 0 := by
  classical
  have hab : a < b := ha.trans (zero_lt_one.trans hb)
  have h01 : Icc (0 : ℝ) 1 ⊆ Icc a b :=
    fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hqt := fun t ht => hq.contMDiffAt (hI.mem_nhds (show t ∈ I from ht))
  obtain ⟨P, hi, hP, _⟩ := exists_orthonormal_parallel_transport g hab hI hq hsub
  let A := coefficient g q P
  let y := fun t => (P t).inverse (J t)
  let v := fun t => (P t).inverse (manifoldCovDerivAlong g q J 1 t)
  have hAt (t : ℝ) (ht : t ∈ Icc a b) (u : EuclideanSpace ℝ (Fin n)) :
      A t u = (P t).inverse (D.curvature (q t) (P t u)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) :=
    chartCoefficient_apply D P (mem_extChartAt_source _) (hqt t (hsub ht)) u
  have hAc : ContinuousOn A (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (contDiffAt_coefficient D hI hq (hsub (h01 ht))
      (hi t (h01 ht)) (fun u => (hP t (h01 ht) u).1)).continuousAt.continuousWithinAt
  have hsol : IsJacobiSolOn A 0 1 y v := by
    constructor
    · intro t ht
      exact (inverse_manifold_parallel_hasDerivAt g hab (h01 ht) hi
        (hqt t (hsub (h01 ht))) (hP t (h01 ht))
        ((hJ t (hsub (h01 ht))).differentiableAt (by simp))).hasDerivWithinAt
    · intro t ht
      have hDJ := contDiffAt_chartField_covDeriv g hI hq hJ
        (hsub (h01 ht)) (mem_extChartAt_source _)
      have hd := inverse_manifold_parallel_hasDerivAt g hab (h01 ht) hi
        (hqt t (hsub (h01 ht))) (hP t (h01 ht))
        (hDJ.differentiableAt (by simp))
      rw [hjac t ht, map_neg] at hd
      have heq := hAt t (h01 ht) ((P t).inverse (J t))
      rw [(hi t (h01 ht)).self_apply_inverse] at heq
      rw [← heq] at hd
      exact hd.hasDerivWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hAc.norm
  let K : ℝ≥0 := ⟨max 1 C, zero_le_one.trans (le_max_left _ _)⟩
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖pairCoeff A t‖₊ ≤ K := by
    intro t ht
    exact_mod_cast (norm_pairCoeff_le A t).trans
      (max_le_max le_rfl (hC ⟨t, ht, rfl⟩))
  have hzero : Poincare.ODE.Linear.IsSolOn (pairCoeff A) 0 1
      (fun _ => (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) := by
    intro t _
    simpa only [map_zero] using hasDerivWithinAt_const t (Icc (0 : ℝ) 1)
      (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
  have hinit : (y 1, v 1) = 0 := by simp [y, v, hJ1, hDJ1]
  intro t ht
  have hpair := Poincare.ODE.Linear.IsSolOn.eqOn_of_right hK
    hsol.isSolOn_pair hzero hinit ht
  have hy := congrArg (fun z => P t z.1) hpair
  have hv := congrArg (fun z => P t z.2) hpair
  exact ⟨by simpa [y, (hi t (h01 ht)).self_apply_inverse] using hy,
    by simpa [v, (hi t (h01 ht)).self_apply_inverse] using hv⟩

theorem jacobi_terminal_deriv_ne_zero
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b c : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c ∈ Icc (0 : ℝ) 1)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ1 : J 1 = 0) (hDJc : manifoldCovDerivAlong g q J 1 c ≠ 0) :
    manifoldCovDerivAlong g q J 1 1 ≠ 0 := by
  intro hDJ1
  exact hDJc (jacobi_eq_zero_of_terminal D ha hb hI hq hsub hJ hjac hJ1 hDJ1 c hc).2

end PoincareConjecture.LaplacianComparison
