import PoincareConjecture.Proofs.M03.Existence.CoordinateMetricRegularityNative
import PoincareConjecture.Proofs.M03.Existence.MatrixMetricTraceNative

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology Matrix

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def intrinsicDeTurckField {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (x : M) : TangentSpace (𝓡 n) x :=
  let e := g.orthonormalBasis x
  ∑ r, CovariantDerivative.difference D.connection B.connection x (e r) (e r)

theorem connectionDifference_apply_field
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    {Y : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    CovariantDerivative.difference D.connection B.connection x (Y x) v =
      D.connection Y x v - B.connection Y x v := by
  have h := IsCovariantDerivativeOn.difference_apply
    D.connection.isCovariantDerivativeOnUniv B.connection.isCovariantDerivativeOnUniv
    (Set.mem_univ x) hY
  simpa only [CovariantDerivative.difference, ContinuousLinearMap.sub_apply] using
    congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x => L v) h

theorem intrinsicDeTurckField_eq_frame_contraction
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a) :
    intrinsicDeTurckField D B x =
      ∑ a, ∑ c, (frameMetricJet g F x).value⁻¹ a c •
        CovariantDerivative.difference D.connection B.connection x (F c x) (F a x) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := CovariantDerivative.difference D.connection B.connection x
  have hgram : Matrix.gram ℝ b = (frameMetricJet g F x).value := by
    ext a c
    change g.inner x (b a) (b c) = g.inner x (F a x) (F c x)
    rw [hpoint a, hpoint c]
  calc
    intrinsicDeTurckField D B x =
        ∑ a, ∑ c, (Matrix.gram ℝ b)⁻¹ a c • A (b c) (b a) :=
      orthonormal_trace_eq_inverse_gram (g.orthonormalBasis x) b A.flip
    _ = _ := by
      rw [hgram]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [hpoint a, hpoint c]

theorem intrinsicDeTurckField_repr_eq_deTurckVector
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a)
    (hF : ∀ a, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% (F a)) x)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0)
    (k : Fin n) :
    b.repr (intrinsicDeTurckField D B x) k =
      deTurckVector (frameMetricJet background F x) (frameMetricJet g F x) k := by
  change b.coord k (intrinsicDeTurckField D B x) = _
  rw [intrinsicDeTurckField_eq_frame_contraction D B F x b hpoint]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold deTurckVector
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [connectionDifference_apply_field D B (hF c), map_sub]
  simp only [Module.Basis.coord_apply]
  rw [connection_repr_eq_christoffelJet D F b hpoint hF hbracket k a c,
    connection_repr_eq_christoffelJet B F b hpoint hF hbracket k a c]

theorem intrinsicDeTurckField_eq_frame_sum
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a)
    (hF : ∀ a, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% (F a)) x)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0) :
    intrinsicDeTurckField D B x =
      ∑ k, deTurckVector (frameMetricJet background F x) (frameMetricJet g F x) k • F k x := by
  calc
    intrinsicDeTurckField D B x =
        ∑ k, b.repr (intrinsicDeTurckField D B x) k • b k :=
      (b.sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [intrinsicDeTurckField_repr_eq_deTurckVector D B F b hpoint hF hbracket k,
        hpoint k]

theorem intrinsicDeTurckField_eq_chartFrame_sum
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) :
    intrinsicDeTurckField D B x =
      ∑ k, deTurckVector (frameMetricJet background (chartFrame p) x)
        (frameMetricJet g (chartFrame p) x) k • chartFrame p k x := by
  exact intrinsicDeTurckField_eq_frame_sum D B (chartFrame p) (chartFrameBasis p x hx)
    (chartFrame_eq_basis p x hx)
    (fun k => ((chartFrame_contMDiffOn p k).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hx)).mdifferentiableAt (by simp))
    (chartFrame_mlieBracket_eq_zero p x hx)

theorem intrinsicDeTurckField_chart_coordinates
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (k : Fin n) :
    (chartFrameBasis p x hx).repr (intrinsicDeTurckField D B x) k =
      deTurckVector
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients background p) (extChartAt (𝓡 n) p x))
        (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
          (chartMetricCoefficients g p) (extChartAt (𝓡 n) p x)) k := by
  rw [← frameMetricJet_eq_coordinateMetricJet background p hx,
    ← frameMetricJet_eq_coordinateMetricJet g p hx]
  exact intrinsicDeTurckField_repr_eq_deTurckVector D B (chartFrame p) (chartFrameBasis p x hx)
    (chartFrame_eq_basis p x hx)
    (fun a => ((chartFrame_contMDiffOn p a).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hx)).mdifferentiableAt (by simp))
    (chartFrame_mlieBracket_eq_zero p x hx) k

end PoincareConjecture.DeTurckNative

end
