import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.DoubleProductRicci












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Bundle
open scoped Topology Manifold ContDiff BigOperators

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem curvatureTensorNorm_eq_zero_of_dimension_zero
    (hn : n = 0) (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = 0 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = 0 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simpa using hn
  let : IsEmpty (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    ⟨fun i => by have hi := i.isLt; omega⟩
  simp [LeviCivitaData.curvatureTensorNorm]



theorem ricci_eq_zero_of_dimension_zero
    (hn : n = 0) (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) : D.ricci x v w = 0 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = 0 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simpa using hn
  let : IsEmpty (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    ⟨fun i => by have hi := i.isLt; omega⟩
  simp [LeviCivitaData.ricci]

variable {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem curvatureSupremum_eq_zero_of_dimension_zero (hn : n = 0) (time : ℝ) :
    m64CurvatureSupremum F time = 0 := by
  have hzero (x : M) : (F.connection time).curvatureTensorNorm x = 0 :=
    curvatureTensorNorm_eq_zero_of_dimension_zero hn _ _ x
  unfold m64CurvatureSupremum
  simp_rw [hzero]
  by_cases hM : Nonempty M
  · let := hM
    simp
  · let : IsEmpty M := not_nonempty_iff.mp hM
    rw [Set.range_eq_empty, Real.sSup_empty]



theorem auxiliaryCircle_ricci_eq_zero_of_dimension_zero
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : n = 0) (time : ℝ)
    (q : Q.charts.Point) (v w : TangentSpace (𝓡 ((n + 1) + 1)) q) :
    (Q.flow.connection time).ricci q v w = 0 := by
  rw [M62.circleProduct_ricci (P.flow.metric time) (P.flow.connection time)
    Q.circle Q.charts (Q.flow.metric time) (Q.flow.connection time) (Q.metric_eq time)]
  rw [M62.circleProduct_ricci (F.metric time) (F.connection time)
    P.circle P.charts (P.flow.metric time) (P.flow.connection time) (P.metric_eq time)]
  exact ricci_eq_zero_of_dimension_zero hn _ _ _ _ _



theorem auxiliaryCircle_annulus_ricciTraceDensity_eq_zero_of_dimension_zero
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : n = 0) (time : ℝ)
    (f : LoopPlane → Q.charts.Point) (z : LoopPlane) :
    m64AnnulusRicciTraceDensity (Q.flow.connection time) f z = 0 := by
  dsimp only [m64AnnulusRicciTraceDensity]
  split_ifs
  · rfl
  · simp only [auxiliaryCircle_ricci_eq_zero_of_dimension_zero P Q hn,
      mul_zero, Finset.sum_const_zero, zero_mul]

end PoincareConjecture.M64
