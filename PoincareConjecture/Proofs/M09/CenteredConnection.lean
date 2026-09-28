import PoincareConjecture.Proofs.M09.CenteredChartOperators
import PoincareConjecture.Proofs.M09.ConnectionFrame
import PoincareConjecture.Proofs.M09.ManifoldTraceDerivative








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem chartVectorField_variable_expansion (p : M) (c : M → E)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    (fun q ↦ chartVectorField p (c q) q) =
      (fun q ↦ ∑ i, b.repr (c q) i • chartVectorField p (b i) q) := by
  funext q
  let L : E →L[ℝ] TangentSpace (𝓡 n) q :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q).inverse
  change L (c q) = ∑ i, b.repr (c q) i • L (b i)
  calc
    _ = L (∑ i, b.repr (c q) i • b i) := congrArg L (b.sum_repr (c q)).symm
    _ = _ := by simp only [map_sum, map_smul]

theorem mdifferentiableAt_chartVectorField_variable (p : M) (c : M → E)
    (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c p) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (fun q ↦ chartVectorField p (c q) q)) p := by
  let b := (stdOrthonormalBasis ℝ E).toBasis
  have hsum : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (fun q ↦ ∑ i, b.repr (c q) i • chartVectorField p (b i) q)) p := by
    apply MDifferentiableAt.sum_section
    intro i _
    have ha : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ b.repr (c q) i) p :=
      (b.coord i).toContinuousLinearMap.mdifferentiableAt.comp p hc
    have hv := ((chartVectorField_smooth p (b i)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))).mdifferentiableAt (by simp)
    exact ha.smul_section hv
  apply hsum.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q ↦ congrArg (Bundle.TotalSpace.mk q)
    (congrFun (chartVectorField_variable_expansion p c b) q)

set_option backward.isDefEq.respectTransparency false in
theorem connection_chartVectorField_variable {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (c : M → E)
    (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c p) (X : TangentSpace (𝓡 n) p) :
    let A : E := frozenConnectionEndomorphism D p X (c p)
    (D.connection (fun q ↦ chartVectorField p (c q) q) p X : E) =
      A + mvfderiv (𝓡 n) c p X := by
  dsimp only
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let a := fun i q ↦ b.repr (c q) i
  let B := frozenConnectionEndomorphism D p X
  have ha (i : Fin (Module.finrank ℝ E)) :
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (a i) p :=
    (b.coord i).toContinuousLinearMap.mdifferentiableAt.comp p hc
  have hframe (i : Fin (Module.finrank ℝ E)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (chartVectorField p (b i))) p :=
    ((chartVectorField_smooth p (b i)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))).mdifferentiableAt (by simp)
  have h := connection_germ_expansion D (fun q ↦ chartVectorField p (c q) q)
    (fun i ↦ chartVectorField p (b i)) a p X
    (mdifferentiableAt_chartVectorField_variable p c hc) hframe ha
    (Filter.Eventually.of_forall (congrFun (chartVectorField_variable_expansion p c b)))
  have hconn (i : Fin (Module.finrank ℝ E)) :
      D.connection (chartVectorField p (b i)) p X = B (b i) :=
    (connection_frozenExtend_eq_chartVectorField D p X (b i)).symm
  have hder (i : Fin (Module.finrank ℝ E)) :
      mvfderiv (𝓡 n) (a i) p X = b.repr (mvfderiv (𝓡 n) c p X) i :=
    mvfderiv_const_clm (b.coord i).toContinuousLinearMap c p hc X
  rw [h]
  simp only [hconn, hder, chartVectorField_self, Finset.sum_add_distrib]
  have hfirst : (∑ i, a i p • B (b i)) = B (c p) := by
    simp only [← map_smul, ← map_sum]
    change B (∑ i, b.repr (c p) i • b i) = B (c p)
    rw [b.sum_repr]
  rw [hfirst, b.sum_repr]

theorem connection_of_eventuallyEq_chartVectorField {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (c : M → E)
    (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c p)
    (σ : (q : M) → TangentSpace (𝓡 n) q)
    (heq : σ =ᶠ[𝓝 p] (fun q ↦ chartVectorField p (c q) q))
    (X : TangentSpace (𝓡 n) p) :
    let A : E := frozenConnectionEndomorphism D p X (c p)
    (D.connection σ p X : E) = A + mvfderiv (𝓡 n) c p X := by
  dsimp only
  have hv := mdifferentiableAt_chartVectorField_variable p c hc
  have hσ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% σ) p := by
    apply hv.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact congrArg (Bundle.TotalSpace.mk q) hq
  rw [D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hv (by simp) heq]
  exact connection_chartVectorField_variable D p c hc X

end PoincareConjecture.Proofs.M09
