import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Gradient.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Derivative



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture



theorem scalarGradientNorm_eq_of_local_isometry
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 3) y,
      g.inner y a b = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b))
    {x : M} (hx : x ∈ U) :
    scalarGradientNorm g D x = scalarGradientNorm h D' (f x) := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f x)) := by
    unfold TangentSpace
    infer_instance
  let L := (LinearEquiv.ofBijective (mfderiv (𝓡 3) (𝓡 3) f x).toLinearMap
    (g.mfderiv_bijective_of_pullback_eq h x
      (fun a b => (hmetric x hx a b).symm))).toContinuousLinearEquiv
  have hL (a : TangentSpace (𝓡 3) x) : L a = mfderiv (𝓡 3) (𝓡 3) f x a := rfl
  have hscalar : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
      (fun y hy => D.scalarCurvature_eq_of_local_isometry D' hU hf hmetric hy)
  have hd (a : TangentSpace (𝓡 3) x) :
      mvfderiv (𝓡 3) D'.scalarCurvature (f x) (L a) =
        mvfderiv (𝓡 3) D.scalarCurvature x a := by
    rw [hL, ← mvfderiv_comp_apply x
      (D'.contMDiff_scalarCurvature.mdifferentiable (by simp) _)
      (((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
      Poincare.mvfderiv_eq_of_eventuallyEq hscalar.symm]
  unfold scalarGradientNorm
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨L a, ?_⟩, congrArg abs (hd a)⟩
    rw [hL, ← hmetric x hx]
    exact a.property
  · rintro ⟨a, rfl⟩
    have ha : g.inner x (L.symm a.1) (L.symm a.1) = 1 := by
      have hi := hmetric x hx (L.symm a.1) (L.symm a.1)
      change g.inner x (L.symm a.1) (L.symm a.1) =
        h.inner (f x) (L (L.symm a.1)) (L (L.symm a.1)) at hi
      simpa only [L.apply_symm_apply, a.property] using hi
    refine ⟨⟨L.symm a.1, ha⟩, ?_⟩
    simpa only [L.apply_symm_apply] using congrArg abs (hd (L.symm a.1)).symm

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalFlow_scalarGradientNorm_of_lt
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) (x : H.regularRegion P04) :
    scalarGradientNorm ((H.terminalFlow P04).metric t) ((H.terminalFlow P04).connection t) x =
      scalarGradientNorm (F.metric t) (F.connection t) (H.reference.forward t ht x) := by
  let f : H.regularRegion P04 → (F.slice t).carrier :=
    fun x => H.reference.forward t ht x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (H.reference.forward_smooth t ht).comp contMDiff_subtype_val
  apply scalarGradientNorm_eq_of_local_isometry
    ((H.terminalFlow P04).connection t) (F.connection t)
    isOpen_univ hf.contMDiffOn (hx := mem_univ x)
  intro y _ a b
  have hd := mfderiv_comp y
    ((H.reference.forward_smooth t ht).mdifferentiable (by simp) y)
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) y)
  change mfderiv (𝓡 3) (𝓡 3) f y = _ at hd
  rw [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  change ((H.terminalFlow P04).metric t).inner y a b =
    (F.metric t).inner (H.reference.forward t ht y)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) y a)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) y b)
  rw [H.reference.metric_pullback]
  exact H.terminalMetricFamily_inner_of_ne P04 ht.2.ne y a b

theorem terminalFlow_scalarGradientNorm_at_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) :
    scalarGradientNorm ((H.terminalFlow P04).metric T) ((H.terminalFlow P04).connection T) x =
      scalarGradientNorm (H.terminalMetric P04) (H.terminalConnection P04) x :=
  congrArg (fun g : RiemannianMetric 3 (H.regularRegion P04) =>
    scalarGradientNorm g g.leviCivitaData x) (H.terminalMetricFamily_at_terminal P04)

end SingularTimeAssumptions

end PoincareConjecture
