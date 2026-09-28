import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ClosedIrreducibleSphere
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

open Classical in
theorem HamiltonMarkedProtectedBall.exists_nonbounding_exterior_surface
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬ ∃ B, B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S))
    (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hCQ : S ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) ⊆ Q.source)
    (hcross : ∀ w ∈ Q '' (S ∩ frontier (closure (latticeHandleDomain ι κ L \ D))),
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C w = 0 ∧ LocallyPiecewiseAffineOn C C.source ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔
          (C x).1.1 = 0) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ (K B : SimplicialComplex ℝ P2) (p : P2 → LatticeHandleAmbient ι κ L),
      K.faces.Finite ∧ B ≤ K ∧
      PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
      p '' K.space = S ∩ E ∧ p '' B.space = S ∩ frontier E ∧
      (∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space) ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ B.faces, t.card ≤ 2) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset P2 | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      HasDisjointPolygonPresentation B.space ∧
      Nat.card (ConnectedComponents B.space) =
        Nat.card (ConnectedComponents (Q '' (S ∩ frontier E))) := by
  classical
  dsimp only
  let E := closure (latticeHandleDomain ι κ L \ D)
  have hE := (b.closed_complement_geometry he hdim hi).1
  have hER := (b.closed_complement_geometry he hdim hi).2.1
  have hne := (b.isConnected_closed_complement he hdim hi).nonempty
  have hphysical : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph _ V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0 := by
    intro x hx
    obtain ⟨C,hxC,hC0,hC,hCS,hCE⟩ := hcross (Q x) (mem_image_of_mem Q hx)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ C hC (hCQ hx) hxC hC0 hCS hCE
  rcases s.exists_planar_exterior_surface_or_subset
      (isCompact_latticeHandleDomain ι κ L) he hSR hE hI.1 hne hphysical with hsub | hmodel
  · obtain ⟨B,hB,hball⟩ := hI.exists_ball_of_sphere_subset hE s hsub
    exact (hn ⟨B,hB.trans hER,hball⟩).elim
  · obtain ⟨K,B,p,hK,hBK,hp,hpi,hps,hpb,hproper,hfull,hpure,hBdim,hcounts,hlinks,hpoly⟩ := hmodel
    refine ⟨K,B,p,hK,hBK,hp,hpi,hps,hpb,hproper,hfull,hpure,hBdim,hcounts,hlinks,hpoly,?_⟩
    have hBs : B.space ⊆ K.space := SimplicialComplex.space_subset_of_le hBK
    let _ : CompactSpace B.space := isCompact_iff_compactSpace.mp
      (B.isCompact_space_of_finite (hK.subset hBK))
    let H : B.space ≃ₜ ↥(S ∩ frontier E) :=
      (Continuous.homeoOfEquivCompactToT2
        (f := Equiv.Set.imageOfInjOn p B.space (hpi.mono hBs))
        ((hp.continuousOn.mono hBs).domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hpb)
    let _ : CompactSpace ↥(S ∩ frontier E) := isCompact_iff_compactSpace.mp
      (s.isCompact.inter_right isClosed_frontier)
    let J : ↥(S ∩ frontier E) ≃ₜ ↥(Q '' (S ∩ frontier E)) :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.Set.imageOfInjOn Q _ (Q.injOn.mono hCQ))
        ((Q.continuousOn.mono hCQ).domRestrict.subtype_mk _)
    let HJ := H.trans J
    let C := HJ.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y => by
      have hfiber : HJ ⁻¹' {y} = {HJ.symm y} := by
        ext x
        exact HJ.toEquiv.eq_symm_apply.symm
      rw [hfiber]
      exact isConnected_singleton
    exact Nat.card_congr C.toEquiv

end PoincareConjecture.M76
