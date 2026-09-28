import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace PoincareConjecture.LpFiniteCoordinatesNative

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] (μ : Measure X)

def coordinateLp (i : ι) : Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ

def insertionLp (i : ι) : Lp ℝ 2 μ →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ i)).compLpL 2 μ

theorem coordinateLp_coe (i : ι) (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    coordinateLp μ i F =ᵐ[μ] fun x => F x i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL F

theorem insertionLp_coe (i : ι) (F : Lp ℝ 2 μ) :
    insertionLp μ i F =ᵐ[μ] fun x => F x • EuclideanSpace.basisFun ι ℝ i :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ i)).coeFn_compLpL F

theorem memLp_coordinate (i : ι) (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    MemLp (fun x => F x i) 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp F

theorem sum_coordinates (v : EuclideanSpace ℝ ι) :
    (∑ i, v i • EuclideanSpace.basisFun ι ℝ i) = v :=
  (EuclideanSpace.basisFun ι ℝ).sum_repr v

theorem sum_insertion_coordinate (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    (∑ i, insertionLp μ i (coordinateLp μ i F)) = F := by
  classical
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : ι => insertionLp μ i (coordinateLp μ i F)),
    ae_all_iff.mpr (fun i : ι => insertionLp_coe μ i (coordinateLp μ i F)),
    ae_all_iff.mpr (fun i : ι => coordinateLp_coe μ i F)] with x hsum hins hcoord
  rw [hsum]
  calc
    _ = ∑ i, F x i • EuclideanSpace.basisFun ι ℝ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hins i, hcoord i]
    _ = _ := sum_coordinates (F x)

theorem l2_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (F : Lp V 2 μ) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  calc
    _ = inner ℝ F F := (real_inner_self_eq_norm_sq F).symm
    _ = ∫ x, inner ℝ (F x) (F x) ∂μ := L2.inner_def F F
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem coordinateLp_norm_sq (i : ι) (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ‖coordinateLp μ i F‖ ^ 2 = ∫ x, (F x i) ^ 2 ∂μ := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [coordinateLp_coe μ i F] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]

theorem sum_coordinateLp_norm_sq (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    (∑ i, ‖coordinateLp μ i F‖ ^ 2) = ‖F‖ ^ 2 := by
  simp_rw [coordinateLp_norm_sq]
  rw [← integral_finsetSum Finset.univ (fun i _ => (memLp_coordinate μ i F).integrable_sq),
    l2_norm_sq]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (EuclideanSpace.real_norm_sq_eq (F x)).symm)

theorem coordinateLp_norm_sq_le (i : ι) (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ‖coordinateLp μ i F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  rw [← sum_coordinateLp_norm_sq μ F]
  exact Finset.single_le_sum (f := fun j : ι => ‖coordinateLp μ j F‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem sum_fiber_coordinateLp_norm_sq_le {κ : Type*} [Fintype κ]
    (j : κ) (F : Lp (EuclideanSpace ℝ (ι × κ)) 2 μ) :
    (∑ i : ι, ‖coordinateLp μ (i, j) F‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ i : ι, ∑ k : κ, ‖coordinateLp μ (i, k) F‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (f := fun k : κ => ‖coordinateLp μ (i, k) F‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ = ∑ ik : ι × κ, ‖coordinateLp μ ik F‖ ^ 2 :=
      (Fintype.sum_prod_type (fun ik : ι × κ => ‖coordinateLp μ ik F‖ ^ 2)).symm
    _ = _ := sum_coordinateLp_norm_sq μ F

theorem norm_coordinateLp_apply_le (i : ι) (F : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ‖coordinateLp μ i F‖ ≤ ‖F‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (coordinateLp_norm_sq_le μ i F)

theorem norm_coordinateLp_le (i : ι) : ‖coordinateLp μ i‖ ≤ 1 := by
  apply (coordinateLp μ i).opNorm_le_bound zero_le_one
  intro F
  simpa only [one_mul] using norm_coordinateLp_apply_le μ i F

theorem coordinateLp_toLp_coe (i : ι) {f : X → EuclideanSpace ℝ ι} (hf : MemLp f 2 μ) :
    coordinateLp μ i (hf.toLp f) =ᵐ[μ] fun x => f x i := by
  filter_upwards [coordinateLp_coe μ i (hf.toLp f), hf.coeFn_toLp] with x hproj hfval
  rw [hproj, hfval]

theorem coordinateLp_toLp_eq (i : ι) {f : X → EuclideanSpace ℝ ι} (hf : MemLp f 2 μ) :
    coordinateLp μ i (hf.toLp f) =
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf).toLp (fun x => f x i) := by
  apply Lp.ext
  exact (coordinateLp_toLp_coe μ i hf).trans
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf).coeFn_toLp.symm

end PoincareConjecture.LpFiniteCoordinatesNative
