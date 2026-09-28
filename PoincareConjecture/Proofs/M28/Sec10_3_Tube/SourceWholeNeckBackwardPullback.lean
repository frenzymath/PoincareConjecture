import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardMaps
import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {W : CriticalBallSourcePacket H}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
    (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))}
  {sigma : ℕ → ℕ}
  {V : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric}

variable (D : WholeNeckBackwardData H W G sigma V)




def fixedFlow (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    RicciFlow 3 D.fixedDomain (Icc (-(V.scale ^ 2 / 2)) 0) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.secondCountable
  exact (D.sourceFlow k).pullbackWithConnection (D.neckMap k)
    (D.neckMap_localDiffeomorph k)
    (fun s => Classical.choice (exists_leviCivitaData
      (((D.sourceFlow k).metric s).pullbackOfLocalDiffeomorph
        (D.neckMap k) (D.neckMap_localDiffeomorph k))))



theorem fixedFlow_metric (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ s : ℝ, (D.fixedFlow k).metric s =
      ((D.sourceFlow k).metric s).pullbackOfLocalDiffeomorph
        (D.neckMap k) (D.neckMap_localDiffeomorph k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s
  rfl



theorem fixedFlow_curvatureTensorNorm (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ) (x : D.fixedDomain),
      ((D.fixedFlow k).connection s).curvatureTensorNorm x =
        ((D.sourceFlow k).connection s).curvatureTensorNorm (D.neckMap k x) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s x
  exact ((D.fixedFlow k).connection s).curvatureTensorNorm_eq_of_local_isometry
    ((D.sourceFlow k).connection s) isOpen_univ
    (D.neckMap_localDiffeomorph k).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)



theorem fixedFlow_curvatureDerivativeNorm (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ) (m : ℕ) (x : D.fixedDomain),
      ((D.fixedFlow k).connection s).curvatureDerivativeNorm m x =
        ((D.sourceFlow k).connection s).curvatureDerivativeNorm m (D.neckMap k x) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s m x
  exact ((D.fixedFlow k).connection s).curvatureDerivativeNorm_eq_pullback
    ((D.sourceFlow k).connection s) isOpen_univ
    (D.neckMap_localDiffeomorph k).contMDiff.contMDiffOn
    (fun y _ => ⟨(D.neckMap_localDiffeomorph k y).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩)
    (fun _ _ _ _ => rfl) m (mem_univ x)

set_option maxHeartbeats 1600000 in




theorem fixedFlow_metric_at_zero_original (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (x : D.fixedDomain) (v w : TangentSpace (𝓡 3) x),
      ((D.fixedFlow k).metric 0).inner x v w =
        D.normalization k *
          ((E (D.sourceIndex k + H.shift)).flow.metric
            (E (D.sourceIndex k + H.shift)).time).inner (D.originalMap k x)
            (mfderiv (𝓡 3) (𝓡 3) (D.originalMap k) x v)
            (mfderiv (𝓡 3) (𝓡 3) (D.originalMap k) x w) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x v w
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : strongNeckOpen (D.neck k) →
          ((E (D.sourceIndex k + H.shift)).flow.slice
            (E (D.sourceIndex k + H.shift)).time).carrier)
        (D.neckMap k x) (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x z) =
      mfderiv (𝓡 3) (𝓡 3) (D.originalMap k) x z :=
    (mfderiv_comp_apply x
      ((contMDiff_subtype_val (n := ∞) (D.neckMap k x)).mdifferentiableAt (by simp))
      ((D.neckMap_localDiffeomorph k x).mdifferentiableAt (by simp)) z).symm
  change ((D.sourceFlow k).metric 0).inner (D.neckMap k x)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x v)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x w) = _
  exact (D.sourceFlow_metric_at_zero k (D.neckMap k x)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x v)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x w)).trans
      (congrArg₂ (fun a b => D.normalization k *
        ((E (D.sourceIndex k + H.shift)).flow.metric
          (E (D.sourceIndex k + H.shift)).time).inner (D.originalMap k x) a b)
        (hderiv v) (hderiv w))

set_option maxHeartbeats 1600000 in




theorem fixedFlow_metric_at_zero (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (x : D.fixedDomain) (v w : TangentSpace (𝓡 3) x),
      ((D.fixedFlow k).metric 0).inner x v w =
        (H.tubeCriticalMetric W.tube W.radius (D.sourceIndex k)).inner
          (D.criticalMap k x)
          (mfderiv (𝓡 3) (𝓡 3) (D.criticalMap k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (D.criticalMap k) x w) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x v w
  let i₁ : H.tubeCriticalRegion W.tube W.radius (D.sourceIndex k) →
      (W.tube (D.sourceIndex k)).carrierOpen := Subtype.val
  let i₂ : (W.tube (D.sourceIndex k)).carrierOpen →
      ((E (D.sourceIndex k + H.shift)).flow.slice
        (E (D.sourceIndex k + H.shift)).time).carrier := Subtype.val
  have h₁ := openSubtype_isLocalDiffeomorph
    (H.tubeCriticalRegion W.tube W.radius (D.sourceIndex k))
  have h₂ := openSubtype_isLocalDiffeomorph (W.tube (D.sourceIndex k)).carrierOpen
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (D.originalMap k) x z =
        mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (D.criticalMap k x))
          (mfderiv (𝓡 3) (𝓡 3) i₁ (D.criticalMap k x)
            (mfderiv (𝓡 3) (𝓡 3) (D.criticalMap k) x z)) := by
    have hfirst := mfderiv_comp_apply x
      ((h₁ (D.criticalMap k x)).mdifferentiableAt (by simp))
      ((D.criticalMap_localDiffeomorph k x).mdifferentiableAt (by simp)) z
    have hsecond := mfderiv_comp_apply x
      ((h₂ (i₁ (D.criticalMap k x))).mdifferentiableAt (by simp))
      (((D.criticalMap_localDiffeomorph k x).comp
        (𝓡 3) (W.tube (D.sourceIndex k)).carrierOpen
        (h₁ (D.criticalMap k x))).mdifferentiableAt (by simp)) z
    exact hsecond.trans (congrArg
      (mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (D.criticalMap k x))) hfirst)
  rw [D.fixedFlow_metric_at_zero_original, hderiv, hderiv]
  rfl

end PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData
