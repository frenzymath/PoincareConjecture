import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Bounds.PhysicalBuffer

/-!
# Coordinate flows on the actual physical chart target

A flow on the open coordinate source transfers to the literal
physical target of its chart. Its carrier has the physical universe
required by the M04 and M13 predecessor services.
Morgan--Tian, Lemma 16.8 and Proposition 16.5, pp. 372-375;
see M44 derivation 52.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Move an ordinary coordinate flow to the actual open physical
target, constructing its connection through the same chart.
Source: Lemma 16.8 and Proposition 16.5; M44 derivation 52. -/
noncomputable def coordinateFlowToTarget
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (F : RicciFlow n (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n))) J) :
    RicciFlow n (⟨e.target, e.open_target⟩ : Opens M) J :=
  F.pullbackWithConnection (sourceTargetDiffeomorph e).symm
    (sourceTargetDiffeomorph e).symm.isLocalDiffeomorph
    (fun t => chartTargetLeviCivitaData
      (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n)))
      (sourceTargetDiffeomorph e)
      ((F.metric t).pullbackOfLocalDiffeomorph (sourceTargetDiffeomorph e).symm
        (sourceTargetDiffeomorph e).symm.isLocalDiffeomorph))

/-- The chart identifies the coordinate metric with the actual
transferred physical metric, pulling both tangent slots.
Source: Lemma 16.8, pp. 372-373; M44 derivation 52. -/
theorem coordinateFlowToTarget_metric
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (F : RicciFlow n (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n))) J)
    (t : ℝ) (x : (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n))))
    (v w : TangentSpace (𝓡 n) x) :
    ((coordinateFlowToTarget e F).metric t).inner (sourceTargetDiffeomorph e x)
      (mfderiv (𝓡 n) (𝓡 n) (sourceTargetDiffeomorph e) x v)
      (mfderiv (𝓡 n) (𝓡 n) (sourceTargetDiffeomorph e) x w) =
        (F.metric t).inner x v w := by
  let d := sourceTargetDiffeomorph e
  have hid : (d.symm ∘ d :
      (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n))) →
      (⟨e.source, e.open_source⟩ : Opens (EuclideanSpace ℝ (Fin n)))) = id :=
    funext d.symm_apply_apply
  have hd : (mfderiv (𝓡 n) (𝓡 n) d.symm (d x)).comp
      (mfderiv (𝓡 n) (𝓡 n) d x) = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x) := by
    rw [← mfderiv_comp x (d.symm.contMDiff.mdifferentiable (by simp) _)
      (d.contMDiff.mdifferentiable (by simp) _), hid, mfderiv_id]
  have hdv (v : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) d.symm (d x) (mfderiv (𝓡 n) (𝓡 n) d x v) = v :=
    congrArg (fun L => L v) hd
  change (F.metric t).inner (d.symm (d x))
    (mfderiv (𝓡 n) (𝓡 n) d.symm (d x) (mfderiv (𝓡 n) (𝓡 n) d x v))
    (mfderiv (𝓡 n) (𝓡 n) d.symm (d x) (mfderiv (𝓡 n) (𝓡 n) d x w)) = _
  rw [hdv v, hdv w, d.symm_apply_apply]

end PoincareMT.M44
