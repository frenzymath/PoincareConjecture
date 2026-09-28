import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductRicci
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in



theorem circleProduct_ricci_derivative
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    (q : P.Point) (A V W : TangentSpace (𝓡 (n + 1)) q) :
    DG.covariantTensorDerivative DG.ricciEvaluation q ![A, V, W] =
      D.covariantTensorDerivative D.ricciEvaluation q.1
        ![(P.split q A).1, (P.split q V).1, (P.split q W).1] := by
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
  have hconn (u v : E) (r s : ℝ) :
      P.split q (DG.connection (B v s) q (B u r q)) =
        (D.connection (X v) p (X u p), 0) :=
    circleProduct_chart_connection g D C P G DG hG p u v r s q hp
  have hd (u v w : E) (r s l : ℝ) :
      mvfderiv (𝓡 (n + 1)) (fun y => DG.ricci y (B v s y) (B w l y)) q (B u r q) =
        mvfderiv (𝓡 n) (fun x => D.ricci x (X v x) (X w x)) p (X u p) := by
    let f : M → ℝ := fun x => D.ricci x (X v x) (X w x)
    have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f p :=
      ((M04.contMDiffOn_ricci D (chartAt E p).open_source (hX v) (hX w)).contMDiffAt
        ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp)
    have heq : (fun y => DG.ricci y (B v s y) (B w l y)) =
        f ∘ (Prod.fst : P.Point → M) := by
      funext y
      rw [circleProduct_ricci g D C P G DG hG]
      dsimp only [B]
      rw [P.productChartField_split, P.productChartField_split]
      rfl
    rw [heq]
    have hc := mvfderiv_comp_apply (f := (Prod.fst : P.Point → M)) (g := f) q hf
      (hfst.mdifferentiableAt (by simp)) (B u r q)
    rw [hc, ← P.split_space]
    change mvfderiv (𝓡 n) f p (P.split q (P.productChartField p u r q)).1 = _
    rw [P.productChartField_split]
  have hformula (u v w : E) (r s l : ℝ) :
      DG.covariantTensorDerivative DG.ricciEvaluation q ![B u r q, B v s q, B w l q] =
        D.covariantTensorDerivative D.ricciEvaluation p ![X u p, X v p, X w p] := by
    have h := M04.covariantTensorDerivativeOnFields_eq DG
      (M04.isSmoothCovariantTensor_ricciEvaluation DG) hopen
      (X := ![B u r, B v s, B w l])
      (by
        intro i
        fin_cases i
        · exact hB u r
        · exact hB v s
        · exact hB w l) hp
    have hs := M04.covariantTensorDerivativeOnFields_eq D
      (M04.isSmoothCovariantTensor_ricciEvaluation D) (chartAt E p).open_source
      (X := ![X u, X v, X w])
      (by
        intro i
        fin_cases i
        · exact hX u
        · exact hX v
        · exact hX w) hp
    simp only [M04.covariantTensorDerivativeOnFields, Fin.sum_univ_succ] at h hs
    change mvfderiv (𝓡 (n + 1)) (fun y => DG.ricci y (B v s y) (B w l y)) q (B u r q) -
      (DG.ricci q (DG.connection (B v s) q (B u r q)) (B w l q) +
        (DG.ricci q (B v s q) (DG.connection (B w l) q (B u r q)) + 0)) =
          DG.covariantTensorDerivative DG.ricciEvaluation q ![B u r q, B v s q, B w l q] at h
    change mvfderiv (𝓡 n) (fun x => D.ricci x (X v x) (X w x)) p (X u p) -
      (D.ricci p (D.connection (X v) p (X u p)) (X w p) +
        (D.ricci p (X v p) (D.connection (X w) p (X u p)) + 0)) =
          D.covariantTensorDerivative D.ricciEvaluation p ![X u p, X v p, X w p] at hs
    rw [hd, circleProduct_ricci g D C P G DG hG,
      circleProduct_ricci g D C P G DG hG, hconn, hconn] at h
    dsimp only [B] at h
    rw [P.productChartField_split, P.productChartField_split] at h
    exact h.symm.trans hs
  obtain ⟨u, r, hA⟩ := P.productChartField_exists p q hp A
  obtain ⟨v, s, hV⟩ := P.productChartField_exists p q hp V
  obtain ⟨w, l, hW⟩ := P.productChartField_exists p q hp W
  rw [← hA, ← hV, ← hW]
  rw [P.productChartField_split, P.productChartField_split, P.productChartField_split]
  exact hformula u v w r s l

end PoincareConjecture.M62
