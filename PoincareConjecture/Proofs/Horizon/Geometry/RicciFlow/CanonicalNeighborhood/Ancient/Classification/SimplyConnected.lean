import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullCoverField
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentCover
import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelPrimitive.Global

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

open RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem exists_fixed_parallel_unit_field_of_simplyConnected
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ W : (q : M) → TangentSpace (𝓡 3) q,
      ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% W) ∧
      ∀ t ≤ 0, ∀ q,
        (K.flow.metric t).inner q (W q) (W q) = 1 ∧
        (∀ z, (K.flow.connection t).ricci q (W q) z = 0) ∧
        ∀ z, (K.flow.connection t).connection W q z = 0 := by
  obtain ⟨C, V, hV, hgeom⟩ :=
    K.exists_fixed_parallel_unit_field_on_null_cover x v w hv hw hvw hzero
  let := unitRicciKernelChartedSpace (K.flow.connection 0) C.covering
  let := unitRicciKernelIsManifold (K.flow.connection 0) C.covering
  let := unitRicciKernelT3Space (K.flow.connection 0) C.covering
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨U, Z, _, hx, _, hZ⟩ :=
    K.exists_fixed_local_parallel_unit_null_section le_rfl x v w hv hw hvw hzero x
  let p : UnitRicciKernel (K.flow.connection 0) :=
    ⟨⟨x, Z x⟩, (hZ 0 le_rfl x hx).1, (hZ 0 le_rfl x hx).2.1⟩
  let S := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let proj := unitRicciKernelProjection (K.flow.connection 0)
  let cp : S → M := fun q => proj q.1
  have hcp := unitRicciKernelComponent_projection_isLocalDiffeomorph
    (K.flow.connection 0) C.covering p
  have hbij : Function.Bijective cp :=
    Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected
      (unitRicciKernelComponent_projection_isCoveringMap
        (K.flow.connection 0) C.covering C.fiber_card p)
  let e : S ≃ₘ⟮𝓡 3, 𝓡 3⟯ M := hcp.diffeomorphOfBijective hbij
  let s : M → UnitRicciKernel (K.flow.connection 0) := fun q => (e.symm q).1
  have hs : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ s := by
    intro q
    exact (e.symm.isLocalDiffeomorph q).comp (𝓡 3) _
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) S (e.symm q))
  have hps : proj ∘ s = id := by
    funext q
    exact e.apply_symm_apply q
  have hproj := unitRicciKernelProjection_isLocalDiffeomorph
    (K.flow.connection 0) C.covering
  have hderiv (q : M) (a : TangentSpace (𝓡 3) q) :
      mfderiv (𝓡 3) (𝓡 3) proj (s q) (mfderiv (𝓡 3) (𝓡 3) s q a) = a := by
    have h := congrArg (fun L => L a)
      (mfderiv_comp q (hproj.mdifferentiable (by simp) (s q))
        (hs.mdifferentiable (by simp) q))
    rw [hps, mfderiv_id] at h
    exact h.symm
  let F := unitRicciKernelFlow K.flow C.covering
  have hmetric (t : ℝ) (q : M) (a b : TangentSpace (𝓡 3) q) :
      (K.flow.metric t).inner q a b =
        (F.metric t).inner (s q) (mfderiv (𝓡 3) (𝓡 3) s q a)
          (mfderiv (𝓡 3) (𝓡 3) s q b) := by
    rw [unitRicciKernelFlow_inner, hderiv, hderiv]
    exact congrArg (fun y => (K.flow.metric t).inner y a b) (congrFun hps q).symm
  let W := VectorField.mpullback (𝓡 3) (𝓡 3) s V
  have hinv (q : M) : (mfderiv (𝓡 3) (𝓡 3) s q).IsInvertible :=
    ⟨hs.mfderivToContinuousLinearEquiv (by simp) q, rfl⟩
  have hpush (q : M) : mfderiv (𝓡 3) (𝓡 3) s q (W q) = V (s q) :=
    (hinv q).self_apply_inverse _
  refine ⟨W, ?_, fun t ht q => ⟨?_, ?_, ?_⟩⟩
  · intro q
    exact (hV (s q)).mpullback_vectorField_preimage (hs.contMDiff q) (hinv q) (by simp)
  · rw [hmetric, hpush]
    exact (hgeom t ht (s q)).1
  · intro z
    rw [(K.flow.connection t).ricci_eq_of_local_isometry (F.connection t)
      isOpen_univ hs.contMDiff.contMDiffOn (fun q _ => hmetric t q) (mem_univ q), hpush]
    exact (hgeom t ht (s q)).2.1 _
  · intro z
    rw [(K.flow.connection t).connection_mpullback_of_metric_pullback
      (F.connection t) (hs.contMDiff q) (Eventually.of_forall hinv)
      (Eventually.of_forall (hmetric t)) ((hV (s q)).mdifferentiableAt (by simp))]
    rw [(hgeom t ht (s q)).2.2]
    exact map_zero _

theorem exists_fixed_parallel_coordinate_of_simplyConnected
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ r : M → ℝ, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r ∧ r x = 0 ∧
      ∀ t ≤ 0,
        (K.flow.connection t).gradient r = (K.flow.connection 0).gradient r ∧
        RiemannianMetric.HasUnitGradient (K.flow.connection t) r ∧
        RiemannianMetric.HasZeroHessian (K.flow.connection t) r := by
  obtain ⟨V, hV, hgeom⟩ :=
    K.exists_fixed_parallel_unit_field_of_simplyConnected x v w hv hw hvw hzero
  obtain ⟨r, hr, hrx, hdr, hgrad⟩ :=
    (K.flow.connection 0).exists_global_potential_of_parallel hV
      (fun q z => (hgeom 0 le_rfl q).2.2 z) x 0
  have hgrad_t (t : ℝ) (ht : t ≤ 0) : (K.flow.connection t).gradient r = V := by
    funext q
    have hd : mvfderiv (𝓡 3) r q = (K.flow.metric t).inner q (V q) := by
      rw [hdr]
      ext z
      exact (K.inner_eq_on_past_of_null_plane le_rfl x v w hv hw hvw hzero t ht q
        (V q) z ((mem_ricciKernel _ _ _).mpr (hgeom 0 le_rfl q).2.1)).symm
    rw [LeviCivitaData.gradient, hd]
    exact ((K.flow.metric t).inner_isInvertible q).inverse_apply_self (V q)
  refine ⟨r, hr, hrx, fun t ht => ⟨(hgrad_t t ht).trans hgrad.symm, ?_, ?_⟩⟩
  · intro q
    change (K.flow.metric t).inner q ((K.flow.connection t).gradient r q)
      ((K.flow.connection t).gradient r q) = 1
    rw [hgrad_t t ht]
    exact (hgeom t ht q).1
  · intro q a b
    rw [(K.flow.connection t).hessian_eq_inner_connection_gradient (hr q),
      hgrad_t t ht, (hgeom t ht q).2.2]
    simp

end PoincareConjecture.AncientKappaSolution
