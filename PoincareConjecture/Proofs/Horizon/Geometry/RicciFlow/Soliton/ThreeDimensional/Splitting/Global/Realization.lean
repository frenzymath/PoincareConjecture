import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.LevelSphere
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.FlowCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient.Antipodal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

set_option maxHeartbeats 1000000 in

theorem globalSplittingObligation_of_null_plane
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    GlobalSplittingObligation S G := by
  classical
  obtain ⟨hc, hcard, hproducts⟩ :=
    G.exists_nullCover_component_canonicalAncientRound_product hP x v w hv hw hvw hzero
  obtain ⟨hc', _, hgeom⟩ :=
    G.exists_complete_nullCover_coordinate hP.curvature x v w hv hw hvw hzero
  letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  letI := unitRicciKernelT2Space_of_covering hc
  letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  letI : MeasurableSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    borel (UnitRicciKernel (G.ancientSourceFlow.connection 0))
  letI : BorelSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) := ⟨rfl⟩
  obtain ⟨hcomplete, hr, hu, hz, hreverse⟩ := hgeom
  have hnonempty : (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ⁻¹'
      {x}).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    change Nat.card (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ⁻¹'
      {x}) ≠ 0
    rw [hcard x]
    norm_num)
  obtain ⟨p, _⟩ := hnonempty
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let F := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
  letI : SecondCountableTopology C := (F.metric 0).secondCountableTopology
  let r : C → ℝ := unitRicciKernelCoordinate
    (G.ancientSourceFlow.connection 0) S.potential ∘ Subtype.val
  let projection : C → M := fun q =>
    unitRicciKernelProjection (G.ancientSourceFlow.connection 0) q.1
  obtain ⟨hsurj, hrC, huC, hprod⟩ := hproducts p
  have hprojection : ContMDiff (𝓡 3) (𝓡 3) ∞ projection :=
    (unitRicciKernelComponent_projection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc p).contMDiff
  have hscale := G.nullCoverComponent_projection_inner_eq_transverse_scale hP.curvature hc
    x v w hv hw hvw hzero
    (G.soliton_scalarCurvature_eq_one_of_null_plane hP x v w hv hw hvw hzero)
    hcomplete hr hu hz p
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens C)) => regular_of_hasUnitGradient huC q
  letI := openLevelSetChartedSpace hrC (⊤ : Opens C) hreg 2 0
  letI := isManifold_openLevelSet hrC (⊤ : Opens C) hreg 2 0
  have hprodSaved := hprod
  obtain ⟨hconn, A, _, hA, ⟨cert⟩, hφ, hsol, e, he, hcoord⟩ := hprod
  letI : ConnectedSpace (zeroLevelSet r) := hconn
  letI : CompactSpace (zeroLevelSet r) := cert.compact
  have hraw := product_pullback_inner_of_transverse_scale G.flow.metric (F.metric 0)
    (A.flow.metric 0) hrC e hcoord projection hprojection (he 0 le_rfl) hscale
  by_cases hp : unitRicciKernelReverse (G.ancientSourceFlow.connection 0) p ∈
      connectedComponent p
  · let τ := unitRicciKernelComponentReverse (G.ancientSourceFlow.connection 0) hc p hp
    have hτ := unitRicciKernelComponentReverse_involutive
      (G.ancientSourceFlow.connection 0) hc p hp
    have hfree := unitRicciKernelComponentReverse_free
      (G.ancientSourceFlow.connection 0) hc p hp
    have hrev : ∀ q : C, r (τ q) = -r q := fun q => hreverse q.1
    obtain ⟨s, hs⟩ := hprodSaved.exists_sphere_coordinates_of_reversal τ hτ hfree hrev
      (unitRicciKernelComponentReverse_preserves_metric G.ancientSourceFlow hc p hp 0)
    have hsA : ∀ (q : zeroLevelSet r) (a b : TangentSpace (𝓡 2) q),
        (A.flow.metric 0).inner q a b = 2 * (roundSphereMetric 2).inner (s q)
          (mfderiv (𝓡 2) (𝓡 2) s q a) (mfderiv (𝓡 2) (𝓡 2) s q b) := by
      intro q a b
      exact (congrArg (fun g : RiemannianMetric 2 (zeroLevelSet r) => g.inner q a b) hA).trans
        (hs q a b)
    refine Or.inr ⟨quotientSphereLineCertificateOfRawProduct G s
      (RoundCylinderSurface.metric s) (RoundCylinderSurface.connection s)
      (fun t _ => RoundCylinderSurface.round s t) (RoundCylinderSurface.inner s)
      e τ hτ hfree projection hprojection hsurj
      (unitRicciKernelComponent_projection_fiber_eq_orbit
        (G.ancientSourceFlow.connection 0) hc p hp hcard) ?_⟩
    intro t ht z a b
    exact (hraw t ht z a b).trans (congrArg (fun c : ℝ => c + a.2 * b.2)
      ((RoundCylinderSurface.inner_eq_neg_time_mul s (A.flow.metric 0) hsA
        t ht z.1 a.1 b.1).symm.trans (RoundCylinderSurface.inner s t ht z.1 a.1 b.1)))
  · obtain ⟨f, hf⟩ := exists_nullComponent_diffeomorph_of_reverse_not_mem
      (G.ancientSourceFlow.connection 0) hc hcard p hp
    let eM := e.trans f
    have heM : (eM : zeroLevelSet r × ℝ → M) = projection ∘ e := by
      funext z
      exact hf (e z)
    have hrawM : ∀ t, t < 0 → ∀ (z : zeroLevelSet r × ℝ)
        (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
        (G.flow.metric t).inner (eM z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) eM z a)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) eM z b) =
            (-t) * (A.flow.metric 0).inner z.1 a.1 b.1 + a.2 * b.2 := by
      rw [heM]
      exact hraw
    rcases normalized_round_surface_sphere_or_antipodal_cover
        (A.flow.connection 0) hφ hsol (cert.round_at_all_times 0 le_rfl) with
      ⟨s, hs⟩ | ⟨q, hq, hqsurj, _, _, hqmetric, hqpair⟩
    · refine Or.inl ⟨productSphereLineCertificateOfRawProduct G s
        (RoundCylinderSurface.metric s) (RoundCylinderSurface.connection s)
        (fun t _ => RoundCylinderSurface.round s t) (RoundCylinderSurface.inner s) eM ?_⟩
      intro t ht z a b
      exact (hrawM t ht z a b).trans (congrArg (fun c : ℝ => c + a.2 * b.2)
        (RoundCylinderSurface.inner_eq_neg_time_mul s (A.flow.metric 0) hs
          t ht z.1 a.1 b.1).symm)
    · exact Or.inr ⟨quotientSphereLineCertificateOfAntipodalSurface G
        (A.flow.metric 0) q hq hqsurj hqpair hqmetric eM hrawM⟩

end PoincareConjecture.ShrinkingSolitonFlow
