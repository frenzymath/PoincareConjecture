import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceC1
import PoincareConjecture.Proofs.M64.Mathlib.ConformalTransverseBound
import PoincareConjecture.Proofs.M64.Mathlib.TransverseProjection

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

theorem m64Conformal_transverse_contDiffOn {N : ℕ} {R C H beta Lambda lower upper : ℝ}
    (hR : 0 < R) (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hu : MemLp u 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => u z j)
      (ball (0 : LoopPlane) R))
    (hsmooth : ContDiffOn ℝ 2 u (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hc : ContinuousOn u (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hbeta : 0 < beta) (hLambda : 0 ≤ Lambda)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), ‖u z - u x‖ ≤ H * dist z x ^ beta)
    (j : Fin N)
    (hzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 →
      ∀ a : Fin N, a ≠ j → u z a = 0)
    (G : LoopPlane → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hmetric : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      (∀ v w, G z v w = G z w v) ∧
      (∀ v, lower * ‖v‖ ^ 2 ≤ G z v v) ∧ (∀ v, G z v v ≤ upper * ‖v‖ ^ 2))
    (hconformal : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
          (fderiv ℝ u z (EuclideanSpace.single 0 1)) =
        G z (fderiv ℝ u z (EuclideanSpace.single 1 1))
          (fderiv ℝ u z (EuclideanSpace.single 1 1)) ∧
      G z (fderiv ℝ u z (EuclideanSpace.single 0 1))
        (fderiv ℝ u z (EuclideanSpace.single 1 1)) = 0)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2)
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4),
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤ Lambda * r ^ (2 * beta)) :
    ContDiffOn ℝ 1 (m64TransverseProjection j ∘ u)
      (closedBall (0 : LoopPlane) (R / 64) ∩ {z | 0 ≤ z 1}) := by
  classical
  let Y := m64TransverseProjection j ∘ u
  let W := fun i => m64TransverseProjection j ∘ V i
  let U := ball (0 : LoopPlane) R ∩ {z : LoopPlane | 0 < z 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hYL : MemLp Y 2 (volume.restrict (ball (0 : LoopPlane) R)) :=
    (m64TransverseProjection j).comp_memLp' hu
  have hWL (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball (0 : LoopPlane) R)) :=
    (m64TransverseProjection j).comp_memLp' (hV i)
  have hYweak (i : Fin 2) (a : Fin N) :
      HasWeakPartialDeriv i (fun z => W i z a) (fun z => Y z a) (ball (0 : LoopPlane) R) := by
    by_cases haj : a = j
    · intro phi _ _ _
      simp only [Y, W, Function.comp_apply, m64TransverseProjection_apply, if_pos haj,
        zero_mul, integral_zero, neg_zero]
    · simpa only [Y, W, Function.comp_apply, m64TransverseProjection_apply, if_neg haj] using
        hweak i a
  have hYs : ContDiffOn ℝ 2 Y U :=
    (m64TransverseProjection j).contDiff.comp_contDiffOn hsmooth
  have hYc : ContinuousOn Y (closedBall (0 : LoopPlane) (R / 2)) :=
    (m64TransverseProjection j).continuous.comp_continuousOn hc
  have hYholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), ‖Y z - Y x‖ ≤ H * dist z x ^ beta := by
    intro x hx z hz
    calc
      _ = ‖m64TransverseProjection j (u z - u x)‖ := by rw [map_sub]; rfl
      _ ≤ ‖u z - u x‖ := m64TransverseProjection_norm j _
      _ ≤ _ := hholder x hx z hz
  have hYzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 → Y z = 0 := by
    intro z hz hface
    ext a
    change m64TransverseProjection j (u z) a = 0
    rw [m64TransverseProjection_apply]
    split_ifs with haj
    · rfl
    · exact hzero z hz hface a haj
  have hfirst (z : LoopPlane) (hz : z ∈ U) :
      fderiv ℝ Y z = (m64TransverseProjection j).comp (fderiv ℝ u z) :=
    m64TransverseProjection_fderiv j
      ((hsmooth.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hYgrowth (z : LoopPlane) (hz : z ∈ U) :
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ Y) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        (C * (2 * upper / lower)) *
          ∑ i : Fin 2, ‖fderiv ℝ Y z (EuclideanSpace.single i 1)‖ ^ 2 := by
    have hmet := hmetric z hz
    have hconf := hconformal z hz
    have htrans : (∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2) ≤
        (2 * upper / lower) *
          ∑ i : Fin 2, ‖fderiv ℝ Y z (EuclideanSpace.single i 1)‖ ^ 2 := by
      simp only [hfirst z hz, ContinuousLinearMap.comp_apply, m64TransverseProjection_energy]
      simpa only [Fin.sum_univ_two] using
        m64Conformal_transverse_bound (G z) hmet.1 hlower hupper hmet.2.1 hmet.2.2 j
          (fderiv ℝ u z (EuclideanSpace.single 0 1))
          (fderiv ℝ u z (EuclideanSpace.single 1 1)) hconf.1 hconf.2
    have hsecond (i : Fin 2) : fderiv ℝ (fderiv ℝ Y) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
        m64TransverseProjection j (fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) :=
      m64TransverseProjection_hessian j hU hsmooth hz _ _
    calc
      _ = ‖m64TransverseProjection j (∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))‖ := by
        rw [map_sum]
        simp only [hsecond]
      _ ≤ ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ :=
        m64TransverseProjection_norm j _
      _ ≤ C * ∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2 := hgrowth z hz
      _ ≤ C * ((2 * upper / lower) *
          ∑ i : Fin 2, ‖fderiv ℝ Y z (EuclideanSpace.single i 1)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htrans hC
      _ = _ := by ring
  have hYdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4),
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖W i z‖ ^ 2) ≤ Lambda * r ^ (2 * beta) := by
    intro x hx r hr hrr
    have hsub : closedBall x r ⊆ ball (0 : LoopPlane) R := by
      apply closedBall_subset_ball'
      rw [dist_zero_right]
      have hxn := mem_closedBall_zero_iff.mp hx
      linarith
    have hVI := integrable_finsetSum Finset.univ fun i _ =>
      ((hV i).mono_measure (Measure.restrict_mono_set volume hsub)).norm.integrable_sq
    have hWI := integrable_finsetSum Finset.univ fun i _ =>
      ((hWL i).mono_measure (Measure.restrict_mono_set volume hsub)).norm.integrable_sq
    apply (setIntegral_mono_on hWI hVI measurableSet_closedBall ?_).trans (hdecay x hx r hr hrr)
    intro z _
    exact Finset.sum_le_sum fun i _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (m64TransverseProjection_norm j (V i z))
  exact m64ZeroTrace_quadratic_contDiffOn hR Y W hYL hWL hYweak hYs hYc
    (by positivity) hH hbeta hLambda hYholder hYzero hYgrowth hYdecay

end PoincareConjecture
