import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.LiftedNeck
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M E : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

noncomputable def liftedCoordinateMap (F : NeckDomain N.epsilon → E) (e : E)
    (z : RoundCylinderSpace) : E :=
  if hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ then F (z.1, ⟨z.2, hz⟩) else e

omit [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] in
@[simp] theorem liftedCoordinateMap_apply (F : NeckDomain N.epsilon → E) (e : E)
    (z : NeckDomain N.epsilon) :
    N.liftedCoordinateMap F e (z.1, (z.2 : ℝ)) = F z := by
  simp [liftedCoordinateMap, z.2.property]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E] [IsManifold (𝓡 3) ∞ E] in

theorem liftedCoordinateMap_continuousOn (F : C(NeckDomain N.epsilon, E)) (e : E) :
    ContinuousOn (N.liftedCoordinateMap F e) (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Continuous (fun z : univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ =>
      F (z.1.1, ⟨z.1.2, z.2.2⟩)) :=
    F.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  apply h.congr
  intro z
  exact (N.liftedCoordinateMap_apply F e (z.1.1, ⟨z.1.2, z.2.2⟩)).symm

omit [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] in

theorem projection_liftedCoordinateMap {p : E → M}
    (F : NeckDomain N.epsilon → E) (e : E)
    (hF : p ∘ F = (fun z => (N.coordinate z : M)))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    p (N.liftedCoordinateMap F e z) = N.coordinate_map z := by
  rw [liftedCoordinateMap, dif_pos hz]
  exact (congr_fun hF (z.1, ⟨z.2, hz⟩)).trans (N.coordinate_map_eq _)

omit [IsManifold (𝓡 3) ∞ E] in

theorem liftedCoordinateMap_contMDiffOn {p : E → M}
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (F : C(NeckDomain N.epsilon, E)) (e : E)
    (hF : p ∘ F = (fun z => (N.coordinate z : M))) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (N.liftedCoordinateMap F e)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  have hU : IsOpen (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have hproj : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (p ∘ N.liftedCoordinateMap F e) (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    N.coordinate_map_smooth.congr (fun z hz => N.projection_liftedCoordinateMap F e hF hz.2)
  intro z hz
  let hlocal := hp (N.liftedCoordinateMap F e z)
  have hs := hlocal.localInverse_contMDiffAt.comp z (hproj.contMDiffAt (hU.mem_nhds hz))
  apply ContMDiffAt.contMDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [(N.liftedCoordinateMap_continuousOn F e).continuousAt
    (hU.mem_nhds hz) |>.preimage_mem_nhds
      (hlocal.localInverse.open_target.mem_nhds hlocal.localInverse_mem_target)] with y hy
  exact (hlocal.localInverse_left_inv hy).symm

theorem liftedCoordinateMap_pullback {p : E → M}
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (F : C(NeckDomain N.epsilon, E)) (e : E)
    (hF : p ∘ F = (fun z => (N.coordinate z : M)))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (g.pullbackOfLocalDiffeomorph p hp)
      (N.liftedCoordinateMap F e) z v w = roundCylinderPullback g N.coordinate_map z v w := by
  have hU : IsOpen (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have hs := (N.liftedCoordinateMap_contMDiffOn hp F e hF).contMDiffAt
    (hU.mem_nhds ⟨mem_univ _, hz⟩)
  have heq : p ∘ N.liftedCoordinateMap F e =ᶠ[𝓝 z] N.coordinate_map := by
    filter_upwards [hU.mem_nhds ⟨mem_univ _, hz⟩] with y hy
    exact N.projection_liftedCoordinateMap F e hF hy.2
  have hd : (mfderiv (𝓡 3) (𝓡 3) p (N.liftedCoordinateMap F e z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.liftedCoordinateMap F e) z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z :=
    (mfderiv_comp z ((hp _).mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))).symm.trans heq.mfderiv_eq
  unfold roundCylinderPullback
  rw [RiemannianMetric.pullbackOfLocalDiffeomorph_inner]
  change g.inner (p (N.liftedCoordinateMap F e z))
    (((mfderiv (𝓡 3) (𝓡 3) p (N.liftedCoordinateMap F e z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.liftedCoordinateMap F e) z)) v)
    (((mfderiv (𝓡 3) (𝓡 3) p (N.liftedCoordinateMap F e z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.liftedCoordinateMap F e) z)) w) = _
  rw [hd, N.projection_liftedCoordinateMap F e hF hz]

theorem liftedCoordinateMap_metricComparison {p : E → M}
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (F : C(NeckDomain N.epsilon, E)) (e : E)
    (hF : p ∘ F = (fun z => (N.coordinate z : M))) :
    NeckMetricJetComparison (g.pullbackOfLocalDiffeomorph p hp) N.epsilon N.scale
      (N.liftedCoordinateMap F e) := by
  constructor
  apply (roundCylinderClose_congr (C := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
      (fun z hz v w => congr_arg (N.scale⁻¹ ^ 2 * ·)
        (N.liftedCoordinateMap_pullback hp F e hF hz v w)) 0).mpr
  exact N.metric_comparison.close

end PoincareConjecture.EpsilonNeck
