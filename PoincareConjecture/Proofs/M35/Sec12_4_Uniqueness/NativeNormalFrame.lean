import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.NormalDeTurckDifference
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35.Uniqueness

open DeTurckNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem metricLieDerivative_intrinsicDeTurck_commuting_frame
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) U)
    (b : (y : M) → y ∈ U → Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y))
    (hpoint : ∀ y (hy : y ∈ U) a, F a y = b y hy a)
    (hbracket : ∀ y ∈ U, ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) y = 0)
    {x : M} (hx : x ∈ U) (i j : Fin n) :
    metricLieDerivative D (intrinsicDeTurckField D B) x (F i x) (F j x) =
      lieDerivativeJet (frameMetricJet background F x) (frameMetricJet g F x) i j := by
  let C : Fin n → M → ℝ := fun k y =>
    deTurckVector (frameMetricJet background F y) (frameMetricJet g F y) k
  have hs (a : Fin n) := (hF a).contMDiffAt (hU.mem_nhds hx)
  have hdet : (frameMetricJet g F x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef g F x (b x hx) (hpoint x hx)).det_pos
  have hdetB : (frameMetricJet background F x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef background F x (b x hx) (hpoint x hx)).det_pos
  have hC (k : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (C k) x :=
    (frameDeTurck_contMDiffAt g background F hs hdet hdetB k).mdifferentiableAt (by simp)
  have hW := (intrinsicDeTurckField_contMDiffAt D B x).mdifferentiableAt (by simp)
  have hrep : ∀ᶠ y in 𝓝 x, intrinsicDeTurckField D B y = ∑ k, C k y • F k y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact intrinsicDeTurckField_eq_frame_sum D B F (b y hy) (hpoint y hy)
      (fun k => ((hF k).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      (hbracket y hy)
  rw [metricLieDerivative_frame D F C (intrinsicDeTurckField D B)
    (fun a => (hs a).mdifferentiableAt (by simp)) hC hW hrep (hbracket x hx) i j]
  unfold lieDerivativeJet
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [C]
  rw [mvfderiv_deTurckVector_frameMetricJet g background F hs hdet hdetB i k,
    mvfderiv_deTurckVector_frameMetricJet g background F hs hdet hdetB j k]

theorem ricciDeTurckSource_commuting_frame
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) U)
    (b : (y : M) → y ∈ U → Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y))
    (hpoint : ∀ y (hy : y ∈ U) a, F a y = b y hy a)
    (hbracket : ∀ y ∈ U, ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) y = 0)
    {x : M} (hx : x ∈ U) (i j : Fin n) :
    ricciDeTurckSource (frameMetricJet background F x) (frameMetricJet g F x) i j =
      -2 * D.ricci x (F i x) (F j x) +
        metricLieDerivative D (intrinsicDeTurckField D B) x (F i x) (F j x) := by
  rw [ricci_eq_ricciJet_frameMetricJet D hU F hF b hpoint hbracket hx,
    metricLieDerivative_intrinsicDeTurck_commuting_frame D B hU F hF b hpoint hbracket hx]
  rfl

theorem frameMetricJet_first_zero_of_connection_zero {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% (F a)) x)
    (hz : ∀ a, D.connection (F a) x = 0) : (frameMetricJet g F x).first = 0 := by
  funext a i j
  change mvfderiv (𝓡 n) (fun y => g.inner y (F i y) (F j y)) x (F a x) = 0
  rw [D.mvfderiv_inner (F a) (F i) (F j) (hF i) (hF j), hz i, hz j]
  simp only [zero_apply, map_zero, zero_add]

theorem frameMetricJet_second_metric_symm (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) (x : M) (a c i j : Fin n) :
    (frameMetricJet g F x).second a c i j = (frameMetricJet g F x).second a c j i := by
  exact congrArg (fun f : M → ℝ => mvfderiv (𝓡 n) f x (F a x))
    (funext fun y => frameMetricJet_first_symm g F y c i j)

end PoincareConjecture.M35.Uniqueness
