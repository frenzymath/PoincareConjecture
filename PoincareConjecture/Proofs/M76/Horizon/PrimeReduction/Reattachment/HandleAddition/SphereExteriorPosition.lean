import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProtectedBallSurfaceWindow
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem HamiltonMarkedProtectedBall.frontier_exterior_iff_interior
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    {x : LatticeHandleAmbient ι κ L} (hx : x ∈ interior (latticeHandleDomain ι κ L)) :
    x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ x ∈ frontier D := by
  obtain ⟨_,_,_,_,_,_,hfront⟩ := b.closed_complement_geometry he hdim hi
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  rw [hfront]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact (h.2.2 hx).elim
  · intro h
    left
    refine ⟨h,?_⟩
    intro hm
    exact (hmark.symm.subset hm.1).2.2 hx

theorem HamiltonMarkedProtectedBall.exists_sphere_exterior_position
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∃ (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      (Phi : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι κ L)
      (G : SimplicialComplex ℝ V3),
      D ⊆ Q.source ∧ (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      Phi '' S ∩ frontier E ⊆ Q.source ∧
      G.faces.Finite ∧ G.space = Q '' (Phi '' S ∩ frontier E) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
          (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧
          LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, Q.symm x ∈ Phi '' S ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, Q.symm x ∈ frontier E ↔ (C x).1.1 = 0 := by
  classical
  dsimp only
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hs,hSR',hG,hGs,hGc,hdegree,hcross⟩ :=
    b.ball.exists_protected_frontier_intersection_graph_with_crossings
      (isCompact_latticeHandleDomain ι κ L) he b.subset_domain s hSR
  have hcontacts : Phi '' S ∩ frontier E = Phi '' S ∩ frontier D := by
    ext x
    constructor
    · rintro ⟨hx,hf⟩
      exact ⟨hx,(b.frontier_exterior_iff_interior he hdim hi (hSR' hx)).mp hf⟩
    · rintro ⟨hx,hf⟩
      exact ⟨hx,(b.frontier_exterior_iff_interior he hdim hi (hSR' hx)).mpr hf⟩
  have hcontactQ : Phi '' S ∩ frontier E ⊆ Q.source := by
    intro x hx
    exact hDQ (b.ball.isCompact.isClosed.frontier_subset (hcontacts.subset hx).2)
  refine ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hs,hSR',hcontactQ,hG,
    hGs.trans (congrArg (fun T => Q '' T) hcontacts.symm),hGc,hdegree,?_⟩
  intro w hw O hO hwO
  let U : Set V3 := O ∩ (Q.target ∩ Q.symm ⁻¹' interior R)
  have hU : IsOpen U := hO.inter (Q.symm.isOpen_inter_preimage isOpen_interior)
  obtain ⟨x,⟨hxS,hxD⟩,hxw⟩ := hGs.subset hw
  have hxQ := hDQ (b.ball.isCompact.isClosed.frontier_subset hxD)
  have hwU : w ∈ U := by
    refine ⟨hwO,?_,?_⟩
    · exact hxw ▸ Q.map_source hxQ
    · change Q.symm w ∈ interior R
      rw [← hxw,Q.left_inv hxQ]
      exact hSR' hxS
  obtain ⟨C,hwC,hCU,hCw,hC,hCi,hCS,hCD⟩ := hcross w hw U hU hwU
  have hCR (z : V3) (hz : z ∈ C.source) : Q.symm z ∈ interior R :=
    (hCU hz).1.2.2
  refine ⟨C,hwC,fun z hz => ⟨(hCU hz).1.1,(hCU hz).2⟩,
    hCR,hCw,hC,hCi,hCS,?_⟩
  intro z hz
  exact (b.frontier_exterior_iff_interior he hdim hi (hCR z hz)).trans (hCD z hz)

end PoincareConjecture.M76
