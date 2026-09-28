import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularContactCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularNullDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.RegularContactCarrier

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem HamiltonMarkedProtectedBall.exists_original_annular_contact_alternatives
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hDQ : D ⊆ Q.source) (hS : S ⊆ interior (latticeHandleDomain ι κ L))
    (hpres : HasDisjointPolygonPresentation (Q '' (S ∩ frontier D))) :
    ∃ (p : P2 → LatticeHandleAmbient ι κ L)
      (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon P2 (n i + 3)),
      PolyhedralPLInCharts e p Ann ∧ InjOn p Ann ∧
      p '' (⋃ i, (P i).boundary ℝ) = S ∩ frontier D ∧
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) ∧
      (∀ i x, x ∈ (P i).boundary ℝ → -1 < depth 8 x ∧ depth 8 x < 1) ∧
      p '' Ann ⊆ frontier D ∧
      frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ p '' Ann ∧
      p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
        interior (latticeHandleDomain ι κ L) ∧
      (∀ z : Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) ∧
      ((∃ i, IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
          PolyhedralPLInCharts e p (closure (P i).inside) ∧
          InjOn p (closure (P i).inside) ∧
          p '' closure (P i).inside ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L) ∧
          p '' closure (P i).inside ∩ S = p '' (P i).boundary ℝ ∧
          IsCompact ((S ∩ frontier D) \ p '' (P i).boundary ℝ) ∧
          ∃ pole, pole ∈ frontier D ∩ frontier (latticeHandleDomain ι κ L) ∧
            pole ∉ p '' closure (P i).inside) ∨
        ((∀ i, Dehn.annulusSquare (8 : ℝ) 1 ⊆ (P i).inside) ∧
          ∀ i j, i ≠ j → closure (P i).inside ⊆ (P j).inside ∨
            closure (P j).inside ⊆ (P i).inside)) := by
  classical
  obtain ⟨G,hG,hGs⟩ := hpres.exists_finite_contact_carrier
  have hSQ : S ∩ frontier D ⊆ Q.source :=
    inter_subset_right.trans (b.ball.boundary_subset.trans hDQ)
  have hGQ : G.space ⊆ Q.target := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hGs.subset hz
    exact Q.map_source (hSQ hx)
  have hphysical : Q.symm '' G.space = S ∩ frontier D := by
    rw [hGs]
    exact Q.symm_image_image_of_subset_source hSQ
  have hcontactR : S ∩ frontier D ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L) :=
    fun _ hx => ⟨hx.2,hS hx.1⟩
  obtain ⟨s,F,K,J,B,H,g,ann,f,C,q,hFc,hF,hFi,hK,hKs,hH,hgc,hg,hgPL,hJmark,hBmark,
    hann,hannboundary,hf,hfi,hC,hq,hqval,hdepth,hpoly,hval,himage⟩ :=
    b.exists_original_annular_contact_coordinates_of_presentation he hdim hi Q hQ G hG
      hGQ hphysical hcontactR (hGs.symm ▸ hpres)
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hJ : J.space = F '' (D ∩ frontier (latticeHandleDomain ι κ L)) :=
    hJmark.trans (congrArg (fun U => F '' U) hmark.symm)
  obtain ⟨p,m,n,P,hp,hpi,hpC,hP,hcover,hdis,hstrict,hpfront,hpcover,hpint,hpends,hpF,halt⟩ :=
    exists_original_annular_null_disk_or_nested_contacts F hFi K hKs H hH g hg hgPL
      b.ball.boundary_subset b.subset_domain (inter_subset_left.trans (hS.trans interior_subset))
      hJ ann hann hannboundary hdepth hpoly himage
  refine ⟨p,m,n,P,hp,hpi,hcover ▸ hpC,hP,hdis,hstrict,hpfront,hpcover,hpint,hpends,?_⟩
  rcases halt with ⟨i,hd,hpD,hpiD,hbody,hcontact,hrem,pole,hpole,hout⟩ | hess
  · refine Or.inl ⟨i,hd,hpD,hpiD,hbody,?_,hrem,pole,hpole,hout⟩
    have heq : p '' closure (P i).inside ∩ S =
        p '' closure (P i).inside ∩ (S ∩ frontier D) := by
      ext x
      exact ⟨fun hx => ⟨hx.1,hx.2,(hbody hx.1).1⟩,fun hx => ⟨hx.1,hx.2.1⟩⟩
    exact heq.trans hcontact
  · exact Or.inr hess

end PoincareConjecture.M76
