import PoincareConjecture.Proofs.M09.CenteredConnection








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

theorem mdifferentiableAt_chartVectorField_variable_on_source
    (p q : M) (hq : q ∈ (chartAt E p).source) (c : M → E)
    (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c q) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (fun x ↦ chartVectorField p (c x) x)) q := by
  let b := (stdOrthonormalBasis ℝ E).toBasis
  have hsum : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (fun x ↦ ∑ i, b.repr (c x) i • chartVectorField p (b i) x)) q := by
    apply MDifferentiableAt.sum_section
    intro i _
    have ha : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun x ↦ b.repr (c x) i) q :=
      (b.coord i).toContinuousLinearMap.mdifferentiableAt.comp q hc
    have hv := ((chartVectorField_smooth p (b i)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hq)).mdifferentiableAt (by simp)
    exact ha.smul_section hv
  apply hsum.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x ↦ congrArg (Bundle.TotalSpace.mk x)
    (congrFun (chartVectorField_variable_expansion p c b) x)

set_option backward.isDefEq.respectTransparency false in
theorem connection_chartVectorField_variable_on_source {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p q : M) (hq : q ∈ (chartAt E p).source)
    (c : M → E) (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c q)
    (X : TangentSpace (𝓡 n) q) (A : E →L[ℝ] E)
    (hA : ∀ v : E, D.connection (chartVectorField p v) q X = chartVectorField p (A v) q) :
    D.connection (fun x ↦ chartVectorField p (c x) x) q X =
      chartVectorField p (A (c q) + mvfderiv (𝓡 n) c q X) q := by
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let a := fun i x ↦ b.repr (c x) i
  have ha (i : Fin (Module.finrank ℝ E)) :
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (a i) q :=
    (b.coord i).toContinuousLinearMap.mdifferentiableAt.comp q hc
  have hframe (i : Fin (Module.finrank ℝ E)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (chartVectorField p (b i))) q :=
    ((chartVectorField_smooth p (b i)).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have h := connection_germ_expansion D (fun x ↦ chartVectorField p (c x) x)
    (fun i ↦ chartVectorField p (b i)) a q X
    (mdifferentiableAt_chartVectorField_variable_on_source p q hq c hc) hframe ha
    (Filter.Eventually.of_forall (congrFun (chartVectorField_variable_expansion p c b)))
  have hder (i : Fin (Module.finrank ℝ E)) :
      mvfderiv (𝓡 n) (a i) q X = b.repr (mvfderiv (𝓡 n) c q X) i :=
    mvfderiv_const_clm (b.coord i).toContinuousLinearMap c q hc X
  rw [h]
  simp only [hA, hder, Finset.sum_add_distrib]
  let L : E →L[ℝ] TangentSpace (𝓡 n) q :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q).inverse
  change (∑ i, a i q • L (A (b i))) +
      (∑ i, b.repr (mvfderiv (𝓡 n) c q X) i • L (b i)) =
    L (A (c q) + mvfderiv (𝓡 n) c q X)
  simp only [a, ← map_smul, ← map_sum, b.sum_repr, map_add]

theorem connection_of_eventuallyEq_chartVectorField_on_source {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p q : M) (hq : q ∈ (chartAt E p).source)
    (c : M → E) (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c q)
    (σ : (x : M) → TangentSpace (𝓡 n) x)
    (heq : σ =ᶠ[𝓝 q] (fun x ↦ chartVectorField p (c x) x))
    (X : TangentSpace (𝓡 n) q) (A : E →L[ℝ] E)
    (hA : ∀ v : E, D.connection (chartVectorField p v) q X = chartVectorField p (A v) q) :
    D.connection σ q X = chartVectorField p (A (c q) + mvfderiv (𝓡 n) c q X) q := by
  have hv := mdifferentiableAt_chartVectorField_variable_on_source p q hq c hc
  have hσ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% σ) q := by
    apply hv.congr_of_eventuallyEq
    filter_upwards [heq] with x hx
    exact congrArg (Bundle.TotalSpace.mk x) hx
  rw [D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hv (by simp) heq]
  exact connection_chartVectorField_variable_on_source D p q hq c hc X A hA

theorem mvfderiv_vector_chartVectorField (p : M) (f : M → E) (y v : E)
    (hy : y ∈ (chartAt E p).target)
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f ((chartAt E p).symm y)) :
    mvfderiv (𝓡 n) f ((chartAt E p).symm y)
        (chartVectorField p v ((chartAt E p).symm y)) =
      fderiv ℝ (fun z ↦ f ((chartAt E p).symm z)) y v := by
  rw [chartVectorField_at_inverse p v y hy]
  have h := mfderiv_comp y hf
    ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at h
  exact (congrArg (fun L ↦ L v) h).symm

end PoincareConjecture.Proofs.M09
