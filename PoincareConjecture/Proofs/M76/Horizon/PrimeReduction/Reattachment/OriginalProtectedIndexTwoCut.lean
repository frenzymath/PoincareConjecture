import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OriginalFamilyNoL3CocoreFree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedCutFromRelativeCollars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCutAmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProtectedProductEscape

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_index_two_disjoint_noL3_cut
    {ι κ α β E : Type*} [Fintype ι] [Fintype κ] [Finite β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {f : LatticeHandleAmbient ι κ L → E} {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2)
    (c : MarkedSphereCut e (latticeHandleDomain ι κ L) β)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (K : SimplicialComplex ℝ E) (g : E → LatticeHandleAmbient ι κ L)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ latticeHandleDomain ι κ L, f x ∈ K.space ∧ g (f x) = x) :
    ∃ d : MarkedSphereCut e (latticeHandleDomain ι κ L) β,
      HasNoPuncturedSphereComponents e f d.carrier ∧
      ∀ i, Disjoint (d.spheres i) D := by
  classical
  obtain ⟨p,t,ht,hp,hpi,hpD,hproper,_,S,sS,hdis,hSR,hfree,
      O,W,B,sB,hO,hOdis,hopen,hcenter,hSC,hCut,hCutPL,hnoCut,hBdis,hBsub,hfront⟩ :=
    b.exists_original_family_noL3_cocore_free he hdim hi c.collar c.spheres c.spherePL
      c.product rfl c.compactCut c.plCut c.collarOpen c.collarInterior c.collarDisjoint
      c.openCoordinates c.centerCoordinates c.sphereClosure c.ports c.portPL
      c.portDisjoint c.portClosure c.frontierCut hno K g hf hg hgi hreal
  have hR := isCompact_latticeHandleDomain ι κ L
  obtain ⟨d,hdS,_,_,hnoD⟩ := exists_marked_cut_from_relative_collars
    O S sS hdis W rfl hCut hCutPL (fun i => (hO i).1) (fun i => (hO i).2)
    hOdis hopen hcenter hSC B sB hBdis hBsub hfront hnoCut hR he hSR
    K g hg hgi hreal isOpen_univ (fun _ => subset_univ _)
  obtain ⟨F,hF,_,hFR,_,hFD⟩ := exists_original_protected_product_escape_at_height
    hR he b.subset_domain p hp hpi hpD hproper t
      (by constructor <;> linarith [ht.1,ht.2])
      (isCompact_iUnion fun i => (sS i).isCompact) (iUnion_subset hSR) hfree
  refine ⟨d.image F hFR hF,
    d.image_no_punctured_sphere_components hnoD F hFR hF K g hf hg hgi hreal,?_⟩
  intro i
  change Disjoint (F '' d.spheres i) D
  rw [congrFun hdS i]
  exact hFD.mono_left (image_mono (subset_iUnion S i))

end PoincareConjecture.M76
