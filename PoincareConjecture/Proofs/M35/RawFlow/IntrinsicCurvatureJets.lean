import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsFrame
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)


noncomputable def intrinsicCurvatureSlots : (m : ℕ) → Fin (4 + m) → ℝ → StandardCapSpace
  | 0 => ![intrinsicAxisAngular g hrotation hcomplete, intrinsicAxisRadial g hrotation hcomplete,
      intrinsicAxisAngular g hrotation hcomplete, intrinsicAxisRadial g hrotation hcomplete]
  | m + 1 => Fin.cons (intrinsicAxisRadial g hrotation hcomplete)
      (intrinsicCurvatureSlots m)

theorem intrinsicCurvatureSlots_contDiff (m : ℕ) (i : Fin (4 + m)) :
    ContDiff ℝ ∞ (intrinsicCurvatureSlots g hrotation hcomplete m i) := by
  induction m with
  | zero =>
      fin_cases i <;> first
        | exact intrinsicAxisAngular_contDiff g hrotation hcomplete
        | exact intrinsicAxisRadial_contDiff g hrotation hcomplete
  | succ m ih =>
      refine Fin.cases (intrinsicAxisRadial_contDiff g hrotation hcomplete) ih i

theorem intrinsicCurvatureSlots_unit (m : ℕ) (i : Fin (4 + m)) (s : ℝ) :
    g.tangentNorm (intrinsicAxisCurve g hrotation hcomplete s)
      (intrinsicCurvatureSlots g hrotation hcomplete m i s) = 1 := by
  induction m with
  | zero =>
      fin_cases i <;> first
        | exact intrinsicAxisAngular_unit g hrotation hcomplete s
        | exact intrinsicAxisRadial_unit g hrotation hcomplete s
  | succ m ih =>
      refine Fin.cases (intrinsicAxisRadial_unit g hrotation hcomplete s) ih i

variable (D : LeviCivitaData g)

include D in
theorem intrinsicCurvatureSlots_parallel (m : ℕ) (i : Fin (4 + m))
    {s : ℝ} (hs : 0 < s) :
    ConnectionVariation.manifoldCovDerivAlong g (intrinsicAxisCurve g hrotation hcomplete)
      (intrinsicCurvatureSlots g hrotation hcomplete m i) 1 s = 0 := by
  induction m with
  | zero =>
      fin_cases i <;> first
        | exact intrinsicAxisAngular_parallel g hrotation hcomplete D hs
        | exact intrinsicAxisRadial_parallel g hrotation hcomplete D hs
  | succ m ih =>
      refine Fin.cases (intrinsicAxisRadial_parallel g hrotation hcomplete D hs) ih i


noncomputable def intrinsicCurvatureJet (m : ℕ) (s : ℝ) : ℝ :=
  D.iteratedCovariantTensorDerivative D.riemannEvaluation m
    (intrinsicAxisCurve g hrotation hcomplete s)
    (fun i => intrinsicCurvatureSlots g hrotation hcomplete m i s)

theorem intrinsicCurvatureJet_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (intrinsicCurvatureJet g hrotation hcomplete D m) := by
  let hC := D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m
  have hS : ContDiff ℝ ∞ (LeviCivitaData.tensorCoordinateSection hC
      (0 : StandardCapSpace)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using
      LeviCivitaData.contDiffAt_tensorCoordinateSection hC
        (0 : StandardCapSpace) (z := x) (by simp)
  have hV : ContDiff ℝ ∞ (fun s => fun i =>
      intrinsicCurvatureSlots g hrotation hcomplete m i s) :=
    contDiff_pi.mpr (intrinsicCurvatureSlots_contDiff g hrotation hcomplete m)
  have he := (TensorFiber.continuousMultilinear
    (E := StandardCapSpace) (k := 4 + m)).analyticOnNhd_uncurry_of_multilinear
    (s := Set.univ) |>.contDiff (n := ∞)
  change ContDiff ℝ ∞ (fun s => D.iteratedCovariantTensorDerivative D.riemannEvaluation m
    (intrinsicAxisCurve g hrotation hcomplete s)
    (fun i => intrinsicCurvatureSlots g hrotation hcomplete m i s))
  simpa only [Function.comp_def,
    TensorFiber.continuousMultilinear_apply, LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model] using
    he.comp ((hS.comp (intrinsicAxisCurve_contDiff g hrotation hcomplete)).prodMk hV)


theorem intrinsicCurvatureJet_hasDerivAt (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (intrinsicCurvatureJet g hrotation hcomplete D m)
      (intrinsicCurvatureJet g hrotation hcomplete D (m + 1) s) s := by
  have h := D.fderiv_iteratedCurvature_pullback_model m
    ((intrinsicAxisCurve_contDiff g hrotation hcomplete).differentiable (by simp) s)
    (fun i => (intrinsicCurvatureSlots_contDiff g hrotation hcomplete m i).differentiable
      (by simp) s) (1 : ℝ)
  simp_rw [intrinsicCurvatureSlots_parallel g hrotation hcomplete D m _ hs] at h
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 (intrinsicAxisCurve g hrotation hcomplete s)
  simp only [hA, MultilinearMap.map_update_zero, Finset.sum_const_zero, add_zero] at h
  change deriv (intrinsicCurvatureJet g hrotation hcomplete D m) s = _ at h
  have hcurve := (intrinsicAxisCurve_hasDerivAt g hrotation hcomplete s).deriv
  change (fderiv ℝ (intrinsicAxisCurve g hrotation hcomplete) s) 1 = _ at hcurve
  rw [hcurve] at h
  have hslots : (Fin.cons (intrinsicAxisRadial g hrotation hcomplete s)
      (fun i => intrinsicCurvatureSlots g hrotation hcomplete m i s) :
        Fin (4 + m + 1) → TangentSpace (𝓡 3) (intrinsicAxisCurve g hrotation hcomplete s)) =
      fun i => intrinsicCurvatureSlots g hrotation hcomplete (m + 1) i s := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hfinal : deriv (intrinsicCurvatureJet g hrotation hcomplete D m) s =
      intrinsicCurvatureJet g hrotation hcomplete D (m + 1) s :=
    h.trans (congrArg (fun slots : Fin (4 + m + 1) →
      TangentSpace (𝓡 3) (intrinsicAxisCurve g hrotation hcomplete s) =>
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1)
        (intrinsicAxisCurve g hrotation hcomplete s) slots) hslots)
  exact ((intrinsicCurvatureJet_contDiff g hrotation hcomplete D m).differentiable
    (by simp) s).hasDerivAt.congr_deriv hfinal



theorem iteratedDeriv_intrinsicCurvatureJet (m : ℕ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv m (intrinsicCurvatureJet g hrotation hcomplete D 0) s =
      intrinsicCurvatureJet g hrotation hcomplete D m s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv m (intrinsicCurvatureJet g hrotation hcomplete D 0)
          =ᶠ[𝓝 s] intrinsicCurvatureJet g hrotation hcomplete D m := by
        filter_upwards [eventually_gt_nhds hs] with a ha
        exact ih ha
      rw [heq.deriv_eq, (intrinsicCurvatureJet_hasDerivAt g hrotation hcomplete D m hs).deriv]



theorem abs_intrinsicCurvatureJet_le (m : ℕ) (s : ℝ) :
    |intrinsicCurvatureJet g hrotation hcomplete D m s| ≤
      D.curvatureDerivativeNorm m (intrinsicAxisCurve g hrotation hcomplete s) := by
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 (intrinsicAxisCurve g hrotation hcomplete s)
  have h := abs_tensor_evaluation_le_tensorNorm g _ _ A hA
    (fun i => intrinsicCurvatureSlots g hrotation hcomplete m i s)
  simpa only [intrinsicCurvatureJet, intrinsicCurvatureSlots_unit,
    Finset.prod_const_one, mul_one, LeviCivitaData.curvatureDerivativeNorm] using h

end PoincareConjecture.M35.Uniqueness
