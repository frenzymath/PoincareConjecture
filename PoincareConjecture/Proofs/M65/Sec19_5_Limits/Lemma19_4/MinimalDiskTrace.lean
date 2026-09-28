import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.MinimalDiskRecord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65MinimalDisk

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {γ : C1FreeLoopSpace (M := M)}

noncomputable def boundaryColumn (S : M65MinimalDisk g connection γ)
    (z : LoopPlane) (i : Fin 2) : TangentSpace (𝓡 3) (S.disk.map z) :=
  mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)

theorem boundaryColumn_continuousOn (S : M65MinimalDisk g connection γ) (i : Fin 2) :
    ContinuousOn (fun z => (⟨S.disk.map z, S.boundaryColumn z i⟩ :
      TangentBundle (𝓡 3) M)) loopDiskSet :=
  (S.boundary_regular.continuousOn_tangentMapWithin le_rfl m65LoopDisk_uniqueMDiffOn).comp
    (((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn) (fun _ hw => hw)

theorem boundaryColumn_eq_mfderiv (S : M65MinimalDisk g connection γ)
    {z : LoopPlane} (hz : z ∈ Metric.ball (0 : LoopPlane) 1) (i : Fin 2) :
    S.boundaryColumn z i =
      mfderiv (𝓡 2) (𝓡 3) S.disk.map z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have hmem : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hd := mfderivWithin_of_mem_nhds (I := 𝓡 2) (I' := 𝓡 3)
    (f := S.disk.map) hmem
  exact congrArg (fun L : TangentSpace (𝓡 2) z →L[ℝ]
    TangentSpace (𝓡 3) (S.disk.map z) => L (EuclideanSpace.basisFun (Fin 2) ℝ i)) hd

theorem boundary_curve_velocity [T2Space M] (S : M65MinimalDisk g connection γ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 (S.disk.map ∘ Proofs.M58.angularPoint) ∧
      ∀ θ : ℝ, curveVelocity (S.disk.map ∘ Proofs.M58.angularPoint) θ =
        ∑ i : Fin 2, (Proofs.M58.angularVector θ) i •
          S.boundaryColumn (Proofs.M58.angularPoint θ) i :=
  m65BoundaryCurve_velocity_of_trace S.disk.map S.boundary_regular S.boundaryColumn
    S.boundaryColumn_continuousOn (fun _ hz i => S.boundaryColumn_eq_mfderiv hz i)

end PoincareConjecture.M65MinimalDisk
