import PoincareConjecture.Proofs.M10.Countability
import PoincareConjecture.Proofs.M10.Sard

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_slice_criticalValues_eq_zero
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    calibratedMetricVolume (F.metric (T - τ))
      ((fun Z ↦ G.gamma Z τ) ''
        {Z | ¬ Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ)}) = 0 := by
  let : SecondCountableTopology M := secondCountableTopology_of_exponential hL G hτ hmax
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) p) :=
    ((F.metric T).orthonormalBasis p).reindex (finCongr hdim)
  let e0 : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) p :=
    b.repr.symm.toContinuousLinearEquiv
  let E : TangentSpace (𝓡 n) p → M := fun Z ↦ G.gamma Z τ
  have hE : MDifferentiable (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) E := by
    intro Z
    exact ((G.gamma_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ Z, hτ, hmax⟩)).comp Z
      (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have he0 : MDifferentiable (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p)) e0 :=
    e0.differentiable.mdifferentiable
  let f : EuclideanSpace ℝ (Fin n) → M := E ∘ e0
  have hf : MDifferentiable (𝓡 n) (𝓡 n) f := hE.comp he0
  have hchain (x : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) f x =
        (G.toLExponentialFamily.sliceDifferential (e0 x) τ).comp e0.toContinuousLinearMap := by
    have h := mfderiv_comp x (hE (e0 x)) (he0 x)
    rw [mfderiv_eq_fderiv, e0.hasFDerivAt.fderiv] at h
    exact h
  have hnull := calibratedMetricVolume_criticalValues_eq_zero (F.metric (T - τ)) hf
  apply measure_mono_null _ hnull
  rintro q ⟨Z, hZ, rfl⟩
  refine ⟨e0.symm Z, ?_, ?_⟩
  · intro hbij
    rw [hchain] at hbij
    have hbase := (Function.Bijective.of_comp_iff
      (G.toLExponentialFamily.sliceDifferential (e0 (e0.symm Z)) τ) e0.bijective).mp hbij
    exact hZ (Eq.mp (congrArg (fun V : TangentSpace (𝓡 n) p ↦
      Function.Bijective (G.toLExponentialFamily.sliceDifferential V τ))
      (e0.apply_symm_apply Z)) hbase)
  · simp only [f, E, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

end PoincareConjecture.M10
