import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.CoverCoordinate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Flow











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

open RicciFlow.Splitting Poincare.Geometry.RicciFlow.Harnack

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem exists_fixed_parallel_unit_field_on_null_cover
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ C : NullOrientationCover (K.flow.connection 0),
      letI := unitRicciKernelChartedSpace (K.flow.connection 0) C.covering
      letI := unitRicciKernelIsManifold (K.flow.connection 0) C.covering
      ∃ V : (p : UnitRicciKernel (K.flow.connection 0)) → TangentSpace (𝓡 3) p,
        ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) ∧
        ∀ t ≤ 0, ∀ p,
          ((unitRicciKernelFlow K.flow C.covering).metric t).inner p (V p) (V p) = 1 ∧
          (∀ z, ((unitRicciKernelFlow K.flow C.covering).connection t).ricci p (V p) z = 0) ∧
          ∀ z, ((unitRicciKernelFlow K.flow C.covering).connection t).connection V p z = 0 := by
  obtain ⟨C⟩ := K.nullOrientationCover_of_null_plane le_rfl x v w hv hw hvw hzero
  refine ⟨C, ?_⟩
  let := unitRicciKernelChartedSpace (K.flow.connection 0) C.covering
  let := unitRicciKernelIsManifold (K.flow.connection 0) C.covering
  let proj := unitRicciKernelProjection (K.flow.connection 0)
  let F := unitRicciKernelFlow K.flow C.covering
  let V : (p : UnitRicciKernel (K.flow.connection 0)) → TangentSpace (𝓡 3) p :=
    fun p => (mfderiv (𝓡 3) (𝓡 3) proj p).inverse p.1.snd
  have hproj := unitRicciKernelProjection_isLocalDiffeomorph (K.flow.connection 0) C.covering
  have hinv (p : UnitRicciKernel (K.flow.connection 0)) :
      (mfderiv (𝓡 3) (𝓡 3) proj p).IsInvertible :=
    ⟨hproj.mfderivToContinuousLinearEquiv (by simp) p, rfl⟩
  have hVproj (p : UnitRicciKernel (K.flow.connection 0)) :
      mfderiv (𝓡 3) (𝓡 3) proj p (V p) = p.1.snd :=
    (hinv p).self_apply_inverse _
  have hdim (t : ℝ) (ht : t ≤ 0) (q : M) :
      ricciNullity (K.flow.connection t) q = 1 :=
    K.ricciNullity_eq_one_on_past_of_null_plane le_rfl x v w hv hw hvw hzero t ht q
  have hV : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) := by
    intro p
    let G := restrictFlow K.flow
      (show Icc (-1 : ℝ) 0 ⊆ Iic 0 from fun _ hs => hs.2)
      ordConnected_Icc ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
    have hsec : ∀ s ∈ Icc (-1 : ℝ) 0, (G.connection s).NonnegativeSectionalCurvature := by
      intro s hs q a c
      exact (K.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        q (K.nonnegative_curvature_operator s hs.2 q) a c
    obtain ⟨U, W, hU, hp, hW, hWp, hn⟩ :=
      exists_local_parallel_unit_ricci_null_section_through ricciFlowCurvatureTheory
        (by norm_num : (-1 : ℝ) < 0) G hsec (hdim 0 le_rfl) p
    have heq : V =ᶠ[𝓝 p] VectorField.mpullback (𝓡 3) (𝓡 3) proj W := by
      filter_upwards [unitRicciKernel_eventually_eq_section (K.flow.connection 0) hU W hW
        (fun q _ => hdim 0 le_rfl q) (fun q hq => (hn q hq).1)
        (fun q hq => (hn q hq).2.1) p hp hWp] with q hq
      exact congrArg (mfderiv (𝓡 3) (𝓡 3) proj q).inverse hq
    have hWp' : ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% W) (proj p) :=
      hW.contMDiffAt (hU.mem_nhds hp)
    have hs := hWp'.mpullback_vectorField_preimage
      (f := proj) (hproj.contMDiff p) (hinv p) (by simp)
    apply hs.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact congrArg (fun z : TangentSpace (𝓡 3) q =>
      (z : TangentBundle (𝓡 3) (UnitRicciKernel (K.flow.connection 0)))) hq
  have hnull (t : ℝ) (ht : t ≤ 0) (p : UnitRicciKernel (K.flow.connection 0))
      (z : TangentSpace (𝓡 3) p) : (F.connection t).ricci p (V p) z = 0 := by
    rw [unitRicciKernelFlow_ricci, hVproj]
    apply (mem_ricciKernel _ _ _).mp _ _
    rw [K.ricciKernel_eq_on_past_of_null_plane le_rfl x v w hv hw hvw hzero t ht]
    exact (mem_ricciKernel _ _ _).mpr p.2.2
  have hunit (t : ℝ) (ht : t ≤ 0) (p : UnitRicciKernel (K.flow.connection 0)) :
      (F.metric t).inner p (V p) (V p) = 1 := by
    rw [unitRicciKernelFlow_inner, hVproj]
    change (K.flow.metric t).inner p.1.proj p.1.snd p.1.snd = 1
    rw [K.inner_eq_on_past_of_null_plane le_rfl x v w hv hw hvw hzero t ht
      p.1.proj p.1.snd p.1.snd ((mem_ricciKernel _ _ _).mpr p.2.2)]
    exact p.2.1
  refine ⟨V, hV, fun t ht p => ⟨hunit t ht p, hnull t ht p, ?_⟩⟩
  intro z
  let G := restrictFlow F
    (show Icc (t - 1) t ⊆ Iic 0 from fun _ hs => hs.2.trans ht)
    ordConnected_Icc ⟨t - 1, ⟨le_rfl, by linarith⟩, t,
      ⟨by linarith, le_rfl⟩, by linarith⟩
  have hsec : ∀ s ∈ Icc (t - 1) t, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a c
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator q
      ((unitRicciKernelFlow_nonnegativeCurvatureOperator_iff K.flow C.covering s q).mpr
        (K.nonnegative_curvature_operator s (hs.2.trans ht) _)) a c
  exact connection_eq_zero_of_terminal_unit_null ricciFlowCurvatureTheory
    (by linarith : t - 1 < t) G hsec V (hV p)
    (Eventually.of_forall (hnull t ht)) (Eventually.of_forall (hunit t ht))
    ((unitRicciKernelFlow_ricciNullity K.flow C.covering t p).trans (hdim t ht _)) z

end PoincareConjecture.AncientKappaSolution
