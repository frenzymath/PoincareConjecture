import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCircleCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

private theorem periodic_add (A : M64Annulus g c0 c1) (p : LoopPlane) :
    A.map (annulusPoint curvePeriod 0 + p) = A.map p := by
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> rfl
  have hshift : annulusPoint curvePeriod 0 + p =
      annulusPoint (p 0 + curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  rw [hshift, A.periodic, hp]

theorem m64Annulus_mfderiv_periodic (A : M64Annulus g c0 c1) (p : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) A.map (annulusPoint curvePeriod 0 + p) =
      mfderiv (𝓡 2) (𝓡 n) A.map p := by
  let T : LoopPlane := annulusPoint curvePeriod 0
  have hfun : (A.map ∘ fun q : LoopPlane => T + q) = A.map := funext (periodic_add A)
  have hshift : HasFDerivAt (fun q : LoopPlane => T + q)
      (ContinuousLinearMap.id ℝ LoopPlane) p := (hasFDerivAt_id p).const_add T
  by_cases hp : MDifferentiableAt (𝓡 2) (𝓡 n) A.map (T + p)
  · have hd := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 n) p hp
      hshift.differentiableAt.mdifferentiableAt
    have hT : mfderiv (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) p =
        ContinuousLinearMap.id ℝ LoopPlane := by
      rw [mfderiv_eq_fderiv]
      exact hshift.fderiv
    rw [hfun, hT] at hd
    symm
    simpa only [ContinuousLinearMap.comp_id] using! hd
  · have hnot : ¬MDifferentiableAt (𝓡 2) (𝓡 n) A.map p := by
      intro h
      have hinv : (A.map ∘ fun q : LoopPlane => -T + q) = A.map := by
        funext q
        have heq := periodic_add A (-T + q)
        simpa only [T, Function.comp_apply, add_neg_cancel_left] using heq.symm
      have hminus : MDifferentiableAt (𝓡 2) (𝓡 2)
          (fun q : LoopPlane => -T + q) (T + p) :=
        ((hasFDerivAt_id (T + p)).const_add (-T)).differentiableAt.mdifferentiableAt
      have hh := h.comp_of_eq (T + p) hminus (by simp)
      rw [hinv] at hh
      exact hp hh
    rw [mfderiv_zero_of_not_mdifferentiableAt hp,
      mfderiv_zero_of_not_mdifferentiableAt hnot]

variable {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64AnnulusCircleCurrent_periodic
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (i : Fin 2) (x s : ℝ) :
    m64AnnulusCircleCurrent P t A.map i (annulusPoint (x + curvePeriod) s) =
      m64AnnulusCircleCurrent P t A.map i (annulusPoint x s) := by
  have hshift : annulusPoint (x + curvePeriod) s =
      annulusPoint curvePeriod 0 + annulusPoint x s := by
    ext j
    fin_cases j <;> simp [annulusPoint, add_comm]
  rw [hshift]
  have hd := m64Annulus_mfderiv_periodic A (annulusPoint x s)
  simp only [m64AnnulusCircleCurrent, hd]
  exact congrArg (fun y : P.charts.Point => (P.flow.metric t).inner y
    (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map (annulusPoint x s)
      (EuclideanSpace.single i 1)) (P.charts.circleUnit y)) (periodic_add A _)

end PoincareConjecture
