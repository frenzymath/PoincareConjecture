import PoincareConjecture.Proofs.M15.Prop8_2_CylinderFlow
import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

section Rescaling

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {J : SpacetimeInterval}




theorem rescaling_scalarDifferential_eq
    (hM04 : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J.domain) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (R : OrdinaryParabolicRescaling F Q hQ a)
    (s : ℝ) (hs : s ∈ (parabolicInterval Q hQ a J).domain)
    (c : M) (v : TangentSpace (𝓡 n) c) :
    mvfderiv (𝓡 n) (F.connection (parabolicTimeInv Q a s)).scalarCurvature c v =
      Q * mvfderiv (𝓡 n) (R.flow.connection s).scalarCurvature c v := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RegularSpace M :=
    .of_hasBasis compact_basis_nhds fun _ _ h => h.2.isClosed
  let : T3Space M := ⟨⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hfun : (F.connection (parabolicTimeInv Q a s)).scalarCurvature =
      fun z => Q * (R.flow.connection s).scalarCurvature z := by
    funext z
    have hscale := (R.metric_calculus s).scalar_eq
      (F.connection (parabolicTimeInv Q a s)) (R.flow.connection s) z
    change (R.flow.connection s).scalarCurvature z = _ at hscale
    exact ((eq_div_iff hQ.ne').mp hscale).symm.trans (mul_comm _ _)
  have hslice : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : M => (s, z)) := contMDiff_const.prodMk contMDiff_id
  have hreg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (R.flow.connection s).scalarCurvature :=
    ContMDiffOn.comp_contMDiff (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ).prod (𝓡 n))
      (I'' := 𝓘(ℝ, ℝ)) (f := fun z : M => (s, z))
      (g := fun p : ℝ × M => (R.flow.connection p.1).scalarCurvature p.2)
      (hM04.scalar_regular n M _ R.flow) hslice (fun z => ⟨hs, Set.mem_univ z⟩)
  rw [hfun, mvfderiv_fun_mul mdifferentiableAt_const (hreg.mdifferentiable (by simp) c)]
  simp [mvfderiv_const]

end Rescaling

section Cylinder

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]




theorem actualBallCylinder_scalarDifferential_pullback
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (F : RicciFlow n C K.domain)
    (hscalar : ∀ (t : (G.timeIntervals.interval K).Point) (c : C),
      (F.connection t.val).scalarCurvature c =
        horizontalScalarCurvature G.leafwise (B.embedding.toSpacetime (t, c)))
    (t : (G.timeIntervals.interval K).Point) (c : C)
    (v : TangentSpace (𝓡 n) c) :
    mvfderiv (𝓡 n) (F.connection t.val).scalarCurvature c v =
      M14HorizontalScalarDifferential G (B.embedding.toSpacetime (t, c))
        (B.metric.spatialTangentEquiv t c v).val := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  let f : C → G.Point := fun z => B.embedding.toSpacetime (t, z)
  have hf : ContMDiff (𝓡 n) (spacetimeModel n) ∞ f :=
    B.embedding.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hfun : (F.connection t.val).scalarCurvature =
      horizontalScalarCurvature G.leafwise ∘ f := funext (hscalar t)
  rw [hfun]
  simpa only [M14HorizontalScalarDifferential, B.metric.spatialTangentEquiv_eq] using
    mvfderiv_comp_apply c (H.scalar_smooth.mdifferentiable (by simp) (f c))
      (hf.mdifferentiable (by simp) c) v

end Cylinder

end PoincareConjecture.Proofs.M15
