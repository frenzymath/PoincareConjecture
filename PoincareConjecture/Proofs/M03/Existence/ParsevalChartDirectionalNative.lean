import PoincareConjecture.Proofs.M03.Existence.FrameCoordinateJetNative
import PoincareConjecture.Proofs.M03.Existence.TensorFirstOrderGraphNative
import PoincareConjecture.Proofs.M03.Existence.NativeDirectionalClosedNative
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u v

namespace PoincareConjecture.TensorProbeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def chartParsevalCoefficient (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (p : M) (a : Fin n) (i : iota)
    (z : ModelE) : ℝ :=
  g.inner ((chartAt ModelE p).symm z) (F i ((chartAt ModelE p).symm z))
    (DeTurckNative.chartFrame p a ((chartAt ModelE p).symm z))

theorem chartParsevalCoefficient_contDiffOn (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (p : M) (a : Fin n) (i : iota) :
    ContDiffOn ℝ ∞ (chartParsevalCoefficient g F p a i) (chartAt ModelE p).target := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpair : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (F i x) (DeTurckNative.chartFrame p a x))
      (chartAt ModelE p).source :=
    (F i).contMDiff.contMDiffOn.inner_bundle (DeTurckNative.chartFrame_contMDiffOn p a)
  exact (hpair.comp (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))
    (chartAt ModelE p).symm.mapsTo).contDiffOn

theorem coordinate_derivative_eq_parseval (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) (a : Fin n) :
    fderiv ℝ (f ∘ (chartAt ModelE p).symm) z ((PiLp.basisFun 2 ℝ (Fin n)) a) =
      ∑ i, chartParsevalCoefficient g F p a i z *
        scalarDirectional (F i) f ((chartAt ModelE p).symm z) := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  have hx : e.symm z ∈ e.source := e.map_target hz
  have hchart := DeTurckNative.mvfderiv_scalar_chartFrame p f hx
    ((hf (e.symm z)).mdifferentiableAt (by simp)) a
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)
      (DeTurckNative.chartFrame p a (e.symm z)) =
    fderiv ℝ (f ∘ e.symm) (e (e.symm z)) ((PiLp.basisFun 2 ℝ (Fin n)) a) at hchart
  rw [e.right_inv hz] at hchart
  calc
    _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)
        (DeTurckNative.chartFrame p a (e.symm z)) := hchart.symm
    _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)
        (∑ i, g.inner (e.symm z) (F i (e.symm z))
          (DeTurckNative.chartFrame p a (e.symm z)) • F i (e.symm z)) :=
      congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z))
        (hF (e.symm z) (DeTurckNative.chartFrame p a (e.symm z))).symm
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl

theorem exists_chartParsevalCoefficient_bound (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M)) (p : M)
    {K : Set ModelE} (hK : IsCompact K) (hKt : K ⊆ (chartAt ModelE p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin n) (i : iota) (z : ModelE), z ∈ K →
      |chartParsevalCoefficient g F p a i z| ≤ C := by
  classical
  have hex (ai : Fin n × iota) : ∃ c : ℝ, ∀ z ∈ K,
      |chartParsevalCoefficient g F p ai.1 ai.2 z| ≤ c := by
    obtain ⟨c, hc⟩ := hK.bddAbove_image
      ((chartParsevalCoefficient_contDiffOn g F p ai.1 ai.2).continuousOn.abs.mono hKt)
    exact ⟨c, fun z hz => hc ⟨z, hz, rfl⟩⟩
  choose c hc using hex
  let C : ℝ := ∑ ai : Fin n × iota, max (c ai) 0
  refine ⟨C, Finset.sum_nonneg (fun ai _ => le_max_right (c ai) 0), ?_⟩
  intro a i z hz
  exact (hc (a, i) z hz).trans ((le_max_left (c (a, i)) 0).trans
    (Finset.single_le_sum (fun ai _ => le_max_right (c ai) 0) (Finset.mem_univ (a, i))))

theorem coordinate_gradient_sq_le (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (a : Fin n) (i : iota), |chartParsevalCoefficient g F p a i z| ≤ C) :
    (∑ a : Fin n,
      (fderiv ℝ (f ∘ (chartAt ModelE p).symm) z ((PiLp.basisFun 2 ℝ (Fin n)) a)) ^ 2) ≤
      (n : ℝ) * (Fintype.card iota : ℝ) * C ^ 2 *
        ∑ i, scalarDirectional (F i) f ((chartAt ModelE p).symm z) ^ 2 := by
  classical
  let d : iota → ℝ := fun i => scalarDirectional (F i) f ((chartAt ModelE p).symm z)
  have henergy : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hcoeff (a : Fin n) : (∑ i, chartParsevalCoefficient g F p a i z ^ 2) ≤
      (Fintype.card iota : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : iota, C ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (chartParsevalCoefficient g F p a i z)) hC).mpr (hbound a i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hrow (a : Fin n) :
      (fderiv ℝ (f ∘ (chartAt ModelE p).symm) z ((PiLp.basisFun 2 ℝ (Fin n)) a)) ^ 2 ≤
        (Fintype.card iota : ℝ) * C ^ 2 * ∑ i, d i ^ 2 := by
    rw [coordinate_derivative_eq_parseval g F hF p hf hz a]
    exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => chartParsevalCoefficient g F p a i z) d).trans
        (mul_le_mul_of_nonneg_right (hcoeff a) henergy)
  calc
    _ ≤ ∑ _a : Fin n, (Fintype.card iota : ℝ) * C ^ 2 * ∑ i, d i ^ 2 :=
      Finset.sum_le_sum (fun a _ => hrow a)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [d]
      ring

end PoincareConjecture.TensorProbeNative
