import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullPersistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Product
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Existence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Exclusion












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


theorem M27TwistedSphereLineFlowCertificate.not_compact_product_homeomorph
    (C : M27TwistedSphereLineFlowCertificate K)
    {B : Type*} [TopologicalSpace B] [CompactSpace B] [Nonempty B]
    (e : M ≃ₜ (B × ℝ)) : False := by
  classical
  obtain ⟨s, hs⟩ := C.cover_surjective.hasRightInverse
  let height : M → ℝ := fun x => |(s x).2|
  have hheight (p : UnitTwoSphere × ℝ) : height (C.cover p) = |p.2| := by
    rcases (C.cover_fibers (s (C.cover p)) p).mp (hs (C.cover p)) with hp | hp
    · exact congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) hp.symm
    · have h := congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) hp
      simpa only [m27TwistedProductInvolution, abs_neg] using h.symm
  have hquot := C.cover_local_diffeomorph.isOpenMap.isQuotientMap
    C.cover_local_diffeomorph.isLocalHomeomorph.continuous C.cover_surjective
  have hcontinuous : Continuous height := by
    apply hquot.continuous_iff.mpr
    rw [show height ∘ C.cover = fun p : UnitTwoSphere × ℝ => |p.2| from funext hheight]
    exact continuous_snd.abs
  have hcentral : IsCompact (range (fun x : B => e.symm (x, (0 : ℝ)))) :=
    isCompact_range (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨r₀, hr₀⟩ := hcentral.bddAbove_image hcontinuous.continuousOn
  let r := max r₀ 0
  have hr : 0 ≤ r := le_max_right _ _
  have hzero (x : M) (hx : (e x).2 = 0) : x ∈ C.slabCore r := by
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    rw [C.cover_mem_slabCore_iff, ← hheight]
    apply (hr₀ ?_).trans (le_max_left _ _)
    refine ⟨C.cover p, ⟨(e (C.cover p)).1, ?_⟩, rfl⟩
    simpa only [← hx] using e.symm_apply_apply (C.cover p)
  let f : M → ℝ := fun x => (e x).2
  have hf : Continuous f := continuous_snd.comp e.continuous
  obtain ⟨a, ha, hbound⟩ := ((C.isCompact_slabCore r).image hf).isBounded.exists_pos_norm_lt
  let b : B := Classical.choice inferInstance
  have hout (z : ℝ) (hz : ‖z‖ = a) : e.symm (b, z) ∈ (C.slabCore r)ᶜ := by
    intro hin
    have hlt := hbound (f (e.symm (b, z))) ⟨e.symm (b, z), hin, rfl⟩
    have heq : f (e.symm (b, z)) = z := by simp [f]
    rw [heq, hz] at hlt
    exact (lt_irrefl a) hlt
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : PreconnectedSpace (Ioi r) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  have hext : IsPreconnected ((C.slabCore r)ᶜ) := by
    rw [C.complement_slabCore hr]
    exact isPreconnected_range (C.cover_local_diffeomorph.contMDiff.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨x, hx, hfx⟩ := hext.intermediate_value
    (hout (-a) (by simp [abs_of_pos ha])) (hout a (by simp [abs_of_pos ha]))
    hf.continuousOn (show (0 : ℝ) ∈ Icc (f (e.symm (b, -a))) (f (e.symm (b, a))) by
      simp [f, ha.le])
  exact hx (hzero x hfx)


theorem M27SphereLineFlowCertificate.not_projective_product_homeomorph
    (C : M27SphereLineFlowCertificate K) (e : M ≃ₜ (RealProjectiveTwo × ℝ)) : False := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : SimplyConnectedSpace (UnitTwoSphere × ℝ) :=
    Poincare.Topology.simplyConnectedSpace_prod_contractible
  let : SimplyConnectedSpace M := C.identification.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨O⟩ := Poincare.Topology.nonempty_orientationCompatibleAtlas (M := M)
  have hno : NoEmbeddedTrivialNormalProjectivePlane K := m83OrientationExclusion M O
  exact hno.not_product_homeomorph e



theorem projectivePlaneLine_of_product_homeomorph
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (e : M ≃ₜ (RealProjectiveTwo × ℝ)) :
    Nonempty (M27ProjectivePlaneLineFlowCertificate K) := by
  rcases P.curvatureTrichotomy K with hpos | hmodel
  · exact ((K.flow.metric 0).not_strictlyPositiveSectionalCurvature_of_compact_prod_real
      e.symm (K.flow.connection 0) (K.complete 0 le_rfl) (hpos 0 le_rfl)).elim
  rcases hmodel with hmodel | hmodel
  · obtain ⟨C⟩ := hmodel
    exact (C.not_projective_product_homeomorph e).elim
  rcases hmodel with hprojective | hmodel
  · exact hprojective
  · obtain ⟨C⟩ := hmodel
    exact (C.not_compact_product_homeomorph e).elim



theorem AncientKappaNormalization.projectivePlaneLine_of_target
    (P : AncientKappaClassificationServices.{u})
    {p : M} {b : ℝ} (A : AncientKappaNormalization K p b)
    (h : Nonempty (M27ProjectivePlaneLineFlowCertificate A.target)) :
    Nonempty (M27ProjectivePlaneLineFlowCertificate K) := by
  obtain ⟨C⟩ := h
  exact projectivePlaneLine_of_product_homeomorph P K C.product_homeomorph

end PoincareConjecture
