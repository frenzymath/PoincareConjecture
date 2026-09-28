import PoincareConjecture.Proofs.M09.ConnectionFrame
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

open Filter

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem mdifferentiableAt_parametric_frameCoeff {ι : Type*}
    (b : Module.Basis ι ℝ V) (p q : M) (s : ℝ)
    (H : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hq : q ∈ (trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p).baseSet)
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' V z.2 (H z.1 z.2)) (s, q)) (i : ι) :
    let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
    MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ))
      (fun z : ℝ × M ↦ e.localFrameCoeff (𝓡 n) b i z.2 (H z.1 z.2)) (s, q) := by
  let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
  let B : ℝ × M → TangentBundle (𝓡 n) M :=
    fun z ↦ Bundle.TotalSpace.mk' V z.2 (H z.1 z.2)
  have hB : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n)
      (fun z ↦ (e (B z)).2) (s, q) :=
    ((e.mdifferentiableAt_totalSpace_iff (𝓡 n) B (e.mem_source.mpr hq)).mp hH).2
  let c : V →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  have hc := c.mdifferentiableAt.comp (s, q) hB
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hq)]
    with z hz
  exact e.localFrameCoeff_eq_coeff (I := 𝓡 n) (b := b) (s := H z.1) hz

set_option backward.isDefEq.respectTransparency false in
theorem parametric_frame_time_derivative {ι : Type*} [Fintype ι]
    (g : RiemannianMetric n M) (b : Module.Basis ι ℝ V) (p q : M) (s : ℝ)
    (H : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hq : q ∈ (trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p).baseSet)
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' V z.2 (H z.1 z.2)) (s, q)) :
    let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
    HasDerivAt (fun t ↦ H t q)
      (∑ i, deriv (fun t ↦ e.localFrameCoeff (𝓡 n) b i q (H t q)) s •
        e.localFrame b i q) s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
  have hc (i : ι) : DifferentiableAt ℝ
      (fun t ↦ e.localFrameCoeff (𝓡 n) b i q (H t q)) s :=
    ((mdifferentiableAt_parametric_frameCoeff b p q s H hq hH i).comp s
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ (hc i).hasDerivAt.smul_const (e.localFrame b i q))
  convert! hsum using 1
  funext t
  exact e.eq_sum_localFrameCoeff_smul (s := H t) (b := b) hq

end PoincareConjecture.Proofs.M09
