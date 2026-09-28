import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeDerivative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem cap_metricTensor_smooth (g : RiemannianMetric n M) :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) := by
  classical
  constructor
  · intro x
    refine ⟨MultilinearMap.mk' (R := ℝ)
      (fun v : Fin 2 → TangentSpace (𝓡 n) x => g.inner x (v 0) (v 1)) ?_ ?_,
      fun _ => rfl⟩
    · intro v i a b
      fin_cases i <;> simp [Function.update, map_add, add_apply]
    · intro v i r a
      fin_cases i <;> simp [Function.update, map_smul, smul_apply, smul_eq_mul]
  · intro U _ X hX
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact (hX 0).inner_bundle (hX 1)



theorem cap_covariant_metricTensor_zero {g : RiemannianMetric n M}
    (D : LeviCivitaData g) :
    D.covariantTensorDerivative (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) = 0 := by
  classical
  funext x v
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let X : Fin 2 → (y : M) → TangentSpace (𝓡 n) y :=
    fun i => FiberBundle.extend E (v i.succ)
  have hX (i : Fin 2) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (X i)) x :=
    (M04.contMDiffOn_extend_baseSet (v i.succ)).contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hmetric := M04.metric_derivative_pairing D (FiberBundle.extend E (v 0))
    ((hX 0).mdifferentiableAt (by simp)) ((hX 1).mdifferentiableAt (by simp))
  change mvfderiv (𝓡 n) (fun y => g.inner y (X 0 y) (X 1 y)) x (v 0) -
    ∑ i : Fin 2, g.inner x
      ((Function.update (fun j : Fin 2 => v j.succ) i (D.connection (X i) x (v 0))) 0)
      ((Function.update (fun j : Fin 2 => v j.succ) i (D.connection (X i) x (v 0))) 1) = 0
  simp only [X, FiberBundle.extend_apply_self] at hmetric
  dsimp only [X]
  rw [hmetric]
  simp [Fin.sum_univ_succ, Function.update]



theorem cap_native_modelGram_derivative_zero
    (u : ℝ) (hu : u < 1) (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (a : Fin 3 → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (fun y (b : Fin 2 → Fin 3) =>
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y (b 0) (b 1)) p a = 0 := by
  let g := M35.cylinderEuclideanMetric u hu
  let D := M35.cylinderEuclideanConnection u hu
  let G : CovariantTensorEvaluation 3 (EuclideanSpace ℝ (Fin 3)) 2 :=
    fun x v => g.inner x (v 0) (v 1)
  have h := cap_model_covariantTensorDerivative_native u hu D q G (cap_metricTensor_smooth g)
    (M35.cylinderCoordinateEquiv.symm p) a
  have hG : (fun y (b : Fin 2 → Fin 3) => G (M35.cylinderCoordinateEquiv.symm y)
      (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (b j))) =
      fun y b => roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y
        (b 0) (b 1) := by
    funext y b
    exact (M35.cylinderEuclideanMetric_basis u hu q _ (b 0) (b 1)).trans
      (congrArg (fun z => roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) z
        (b 0) (b 1)) (M35.cylinderCoordinateEquiv.apply_symm_apply y))
  rw [hG, M35.cylinderCoordinateEquiv.apply_symm_apply] at h
  have hz := congrArg (fun T => T (M35.cylinderCoordinateEquiv.symm p)
    (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))) (cap_covariant_metricTensor_zero D)
  exact h.symm.trans hz

end PoincareConjecture.M47
