import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductRicciDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m63CircleProduct_covariantTensorDerivative
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (U : CovariantTensorEvaluation (n + 1) P.Point k)
    (hT : IsSmoothCovariantTensor T) (hU : IsSmoothCovariantTensor U)
    (hprojection : ∀ (q : P.Point) (v : Fin k → TangentSpace (𝓡 (n + 1)) q),
      U q v = T q.1 (fun j => (P.split q (v j)).1))
    (q : P.Point) (v : Fin (k + 1) → TangentSpace (𝓡 (n + 1)) q) :
    DG.covariantTensorDerivative U q v =
      D.covariantTensorDerivative T q.1 (fun j => (P.split q (v j)).1) := by
  classical
  let := P.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let X := fun u : E => PoincareConjecture.Proofs.M09.chartVectorField p u
  let B := fun (u : E) (r : ℝ) => P.productChartField p u r
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hopen : IsOpen {y : P.Point | y.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage hfst.continuous
  have hX (u : E) : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X u))
      (chartAt E p).source := PoincareConjecture.Proofs.M09.chartVectorField_smooth p u
  have hB (u : E) (r : ℝ) : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (B u r)) {y : P.Point | y.1 ∈ (chartAt E p).source} :=
    P.productChartField_contMDiffOn p u r
  have hconn (u w : E) (r s : ℝ) :
      P.split q (DG.connection (B w s) q (B u r q)) =
        (D.connection (X w) p (X u p), 0) :=
    circleProduct_chart_connection g D C P G DG hG p u w r s q hp
  have hformula (u : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ) :
      DG.covariantTensorDerivative U q (fun j => B (u j) (r j) q) =
        D.covariantTensorDerivative T p (fun j => X (u j) p) := by
    have hd :
        mvfderiv (𝓡 (n + 1))
          (fun y => U y (fun j => B (u j.succ) (r j.succ) y)) q (B (u 0) (r 0) q) =
        mvfderiv (𝓡 n) (fun y => T y (fun j => X (u j.succ) y)) p (X (u 0) p) := by
      let f : M → ℝ := fun y => T y (fun j => X (u j.succ) y)
      have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f p :=
        ((hT.2 (chartAt E p).source (chartAt E p).open_source
          (fun j => X (u j.succ)) (fun j => hX (u j.succ))).contMDiffAt
            ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp)
      have heq : (fun y => U y (fun j => B (u j.succ) (r j.succ) y)) =
          f ∘ (Prod.fst : P.Point → M) := by
        funext y
        rw [hprojection]
        apply congrArg (T y.1)
        funext j
        exact congrArg Prod.fst (P.productChartField_split p (u j.succ) (r j.succ) y)
      rw [heq]
      have hc := mvfderiv_comp_apply (f := (Prod.fst : P.Point → M)) (g := f) q hf
        (hfst.mdifferentiableAt (by simp)) (B (u 0) (r 0) q)
      rw [hc, ← P.split_space]
      change mvfderiv (𝓡 n) f p (P.split q (P.productChartField p (u 0) (r 0) q)).1 = _
      rw [P.productChartField_split]
    have hcorrection (i : Fin k) :
        U q (Function.update (fun j => B (u j.succ) (r j.succ) q) i
          (DG.connection (B (u i.succ) (r i.succ)) q (B (u 0) (r 0) q))) =
        T p (Function.update (fun j => X (u j.succ) p) i
          (D.connection (X (u i.succ)) p (X (u 0) p))) := by
      rw [hprojection]
      apply congrArg (T p)
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
        exact congrArg Prod.fst (hconn (u 0) (u i.succ) (r 0) (r i.succ))
      · simp only [Function.update_of_ne hj]
        exact congrArg Prod.fst (P.productChartField_split p (u j.succ) (r j.succ) q)
    have h := M04.covariantTensorDerivativeOnFields_eq DG hU hopen
      (X := fun j => B (u j) (r j)) (fun j => hB (u j) (r j)) hp
    have hs := M04.covariantTensorDerivativeOnFields_eq D hT
      (chartAt E p).open_source (X := fun j => X (u j)) (fun j => hX (u j)) hp
    simp only [M04.covariantTensorDerivativeOnFields] at h hs
    rw [hd] at h
    have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      hcorrection i)
    rw [hsum] at h
    exact h.symm.trans hs
  have hrepresent (j : Fin (k + 1)) : ∃ (u : E) (r : ℝ), B u r q = v j :=
    P.productChartField_exists p q hp (v j)
  choose u r hu using hrepresent
  have hv : v = (fun j => B (u j) (r j) q) := funext fun j => (hu j).symm
  rw [hv]
  have hsplit : (fun j => (P.split q (B (u j) (r j) q)).1) =
      (fun j => X (u j) p) := by
    funext j
    exact congrArg Prod.fst (P.productChartField_split p (u j) (r j) q)
  rw [hsplit]
  exact hformula u r

theorem m63CircleProduct_iteratedCovariantTensorDerivative
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (U : CovariantTensorEvaluation (n + 1) P.Point k)
    (hT : IsSmoothCovariantTensor T) (hU : IsSmoothCovariantTensor U)
    (hprojection : ∀ (q : P.Point) (v : Fin k → TangentSpace (𝓡 (n + 1)) q),
      U q v = T q.1 (fun j => (P.split q (v j)).1))
    (m : ℕ) (q : P.Point) (v : Fin (k + m) → TangentSpace (𝓡 (n + 1)) q) :
    DG.iteratedCovariantTensorDerivative U m q v =
      D.iteratedCovariantTensorDerivative T m q.1 (fun j => (P.split q (v j)).1) := by
  have hTsmooth (j : ℕ) : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T j) := by
    induction j with
    | zero => exact hT
    | succ j ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
  have hUsmooth (j : ℕ) : IsSmoothCovariantTensor (DG.iteratedCovariantTensorDerivative U j) := by
    induction j with
    | zero => exact hU
    | succ j ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative DG ih
  revert q v
  induction m with
  | zero => exact hprojection
  | succ m ih =>
    exact m63CircleProduct_covariantTensorDerivative g D C P G DG hG
      (D.iteratedCovariantTensorDerivative T m) (DG.iteratedCovariantTensorDerivative U m)
      (hTsmooth m) (hUsmooth m) ih

end PoincareConjecture
