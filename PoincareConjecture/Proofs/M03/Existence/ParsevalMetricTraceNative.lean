import PoincareConjecture.Proofs.M03.Existence.GlobalParsevalFrameNative
import PoincareConjecture.Proofs.M03.Existence.FrameCoordinateJetNative
import PoincareConjecture.Proofs.M03.Existence.MatrixMetricTraceNative
import Mathlib.Topology.Algebra.Module.FiniteDimension










set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

universe u v w

namespace PoincareConjecture.ParsevalFrameNative

section LinearAlgebra

variable {V Z iota kappa jota : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [Fintype iota] [Fintype kappa] [Fintype jota]

theorem span_eq_top_of_parseval (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) :
    Submodule.span ℝ (Set.range F) = ⊤ := by
  apply top_unique
  intro v _
  rw [← hF v]
  exact Submodule.sum_mem _ (fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))


theorem parseval_trace_eq_orthonormal_trace (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (e : OrthonormalBasis kappa ℝ V) (A : V →L[ℝ] V →L[ℝ] Z) :
    (∑ a, A (F a) (F a)) = ∑ j, A (e j) (e j) := by
  have hexpand (a : iota) :
      A (F a) (F a) = ∑ j, A (e j) (inner ℝ (F a) (e j) • F a) := by
    calc
      A (F a) (F a) = A (∑ j, inner ℝ (e j) (F a) • e j) (F a) := by
        rw [e.sum_repr']
      _ = _ := by
        simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
          ContinuousLinearMap.smul_apply, real_inner_comm]
  calc
    (∑ a, A (F a) (F a)) = ∑ a, ∑ j, A (e j) (inner ℝ (F a) (e j) • F a) :=
      Finset.sum_congr rfl (fun a _ => hexpand a)
    _ = ∑ j, A (e j) (∑ a, inner ℝ (F a) (e j) • F a) := by
      rw [Finset.sum_comm]
      simp only [map_sum]
    _ = ∑ j, A (e j) (e j) := by simp only [hF]

theorem parseval_trace_eq_inverse_gram [DecidableEq kappa] [DecidableEq jota]
    (F : iota → V) (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (e : OrthonormalBasis kappa ℝ V) (b : Module.Basis jota ℝ V)
    (A : V →L[ℝ] V →L[ℝ] Z) :
    (∑ a, A (F a) (F a)) =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • A (b i) (b j) :=
  (parseval_trace_eq_orthonormal_trace F hF e A).trans
    (DeTurckNative.orthonormal_trace_eq_inverse_gram e b A)


theorem parseval_coordinates_eq_inverse_gram [DecidableEq kappa] [DecidableEq jota]
    (F : iota → V) (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (e : OrthonormalBasis kappa ℝ V) (b : Module.Basis jota ℝ V) (i j : jota) :
    (∑ a, b.repr (F a) i * b.repr (F a) j) = (Matrix.gram ℝ b)⁻¹ i j := by
  letI : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  let Li : V →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  let Lj : V →L[ℝ] ℝ := (b.coord j).toContinuousLinearMap
  have h := parseval_trace_eq_orthonormal_trace F hF e (Li.smulRight Lj)
  change (∑ a, b.repr (F a) i * b.repr (F a) j) =
    ∑ r, b.repr (e r) i * b.repr (e r) j at h
  exact h.trans (DeTurckNative.sum_orthonormal_coordinates_eq_inverse_gram e b i j)


theorem parseval_tensor_pairing (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (e : OrthonormalBasis kappa ℝ V)
    (h k : V →L[ℝ] V →L[ℝ] ℝ) :
    (∑ a, ∑ b, h (F a) (F b) * k (F a) (F b)) =
      ∑ i, ∑ j, h (e i) (e j) * k (e i) (e j) := by
  have hright (a : iota) :
      (∑ b, h (F a) (F b) * k (F a) (F b)) =
        ∑ j, h (F a) (e j) * k (F a) (e j) := by
    exact parseval_trace_eq_orthonormal_trace F hF e ((h (F a)).smulRight (k (F a)))
  have hleft (j : kappa) :
      (∑ a, h (F a) (e j) * k (F a) (e j)) =
        ∑ i, h (e i) (e j) * k (e i) (e j) := by
    exact parseval_trace_eq_orthonormal_trace F hF e ((h.flip (e j)).smulRight (k.flip (e j)))
  calc
    (∑ a, ∑ b, h (F a) (F b) * k (F a) (F b)) =
        ∑ a, ∑ j, h (F a) (e j) * k (F a) (e j) :=
      Finset.sum_congr rfl (fun a _ => hright a)
    _ = ∑ j, ∑ a, h (F a) (e j) * k (F a) (e j) := Finset.sum_comm
    _ = ∑ j, ∑ i, h (e i) (e j) * k (e i) (e j) :=
      Finset.sum_congr rfl (fun j _ => hleft j)
    _ = ∑ i, ∑ j, h (e i) (e j) * k (e i) (e j) := Finset.sum_comm

end LinearAlgebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

local notation "E" => EuclideanSpace ℝ (Fin n)


def metricTensorPairing (g : RiemannianMetric n M)
    (h k : TensorProbeNative.SmoothTensor (n := n) (M := M)) (x : M) : ℝ :=
  ∑ i, ∑ j, h x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
    k x (g.orthonormalBasis x i) (g.orthonormalBasis x j)

theorem native_parseval_span (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (x : M) : Submodule.span ℝ (Set.range (fun a => F a x)) = ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact span_eq_top_of_parseval (fun a => F a x) (hF x)

theorem probes_inner_eq_metricTensorPairing (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (h k : TensorProbeNative.SmoothTensor (n := n) (M := M)) (x : M) :
    inner ℝ (TensorProbeNative.probes F h x) (TensorProbeNative.probes F k x) =
      metricTensorPairing g h k x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hexpand : inner ℝ (TensorProbeNative.probes F h x) (TensorProbeNative.probes F k x) =
      ∑ a, ∑ b, h x (F a x) (F b x) * k x (F a x) (F b x) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change k x (F a x) (F b x) * h x (F a x) (F b x) = _
    exact mul_comm _ _
  exact hexpand.trans (parseval_tensor_pairing (fun a => F a x) (hF x)
    (g.orthonormalBasis x) (h x) (k x))

theorem probes_norm_sq_eq_metricTensorPairing (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (h : TensorProbeNative.SmoothTensor (n := n) (M := M)) (x : M) :
    ‖TensorProbeNative.probes F h x‖ ^ 2 = metricTensorPairing g h h x := by
  rw [← real_inner_self_eq_norm_sq]
  exact probes_inner_eq_metricTensorPairing g F hF h h x


theorem chart_parseval_coordinates_eq_inverse_metric (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (p : M) {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    (∑ a, (DeTurckNative.chartFrameBasis p x hx).repr (F a x) i *
      (DeTurckNative.chartFrameBasis p x hx).repr (F a x) j) =
        (DeTurckNative.chartMetricCoefficients g p (extChartAt (𝓡 n) p x))⁻¹ i j := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgram : Matrix.gram ℝ (DeTurckNative.chartFrameBasis p x hx) =
      DeTurckNative.chartMetricCoefficients g p (extChartAt (𝓡 n) p x) := by
    rw [← DeTurckNative.frameMetricJet_value_eq_chartMetricCoefficients g p hx]
    ext a b
    change g.inner x (DeTurckNative.chartFrameBasis p x hx a)
      (DeTurckNative.chartFrameBasis p x hx b) =
        g.inner x (DeTurckNative.chartFrame p a x) (DeTurckNative.chartFrame p b x)
    rw [DeTurckNative.chartFrame_eq_basis p x hx a,
      DeTurckNative.chartFrame_eq_basis p x hx b]
  rw [← hgram]
  exact parseval_coordinates_eq_inverse_gram (fun a => F a x) (hF x)
    (g.orthonormalBasis x) (DeTurckNative.chartFrameBasis p x hx) i j

end PoincareConjecture.ParsevalFrameNative

end
