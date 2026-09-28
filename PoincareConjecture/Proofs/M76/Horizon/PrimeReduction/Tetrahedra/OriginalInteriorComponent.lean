import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.ClosedInteriorPiece
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage








set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_interior_component_eq_sphere
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (x : X) (hx : x ∈ (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i))
    (hfront : Disjoint
      (connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x)
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))) :
    ∃ i, connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x = S i ∧
      S i ⊆ interior (g '' convexHull ℝ (t : Set E)) := by
  obtain ⟨γ,hγ,C,P,hC,_,hPdis,_,hPcover,hPcomp,hmember⟩ :=
    exists_original_sphere_pieces_in_face he K hK g hg hgi S sS hS hdis ht
  let : Finite γ := hγ
  obtain ⟨c,hxc⟩ := mem_iUnion.mp (hPcover.symm.subset hx)
  obtain ⟨i,hci,_⟩ := hmember c
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  have hSconn : IsConnected (S i) := isConnected_iff_connectedSpace.mpr
    ((sS i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))
  have hcfront : Disjoint (P c) (frontier (g '' convexHull ℝ (t : Set E))) := by
    rw [ball.frontier_eq,←hPcomp c x hxc]
    exact hfront
  obtain ⟨hEq,hint⟩ := closed_piece_eq_connected_parent_of_avoids_frontier
    ball.isCompact.isClosed (sS i).isCompact.isClosed hSconn P
    (fun c => (hC c).2.2.2.2.2.1.isClosed) hPdis
    (fun y hy => hPcover.symm.subset ⟨hy.2,mem_iUnion.mpr ⟨i,hy.1⟩⟩)
    c ⟨x,hxc⟩ hci
    (fun y hy => (hPcover.subset (mem_iUnion.mpr ⟨c,hy⟩)).1) hcfront
  exact ⟨i,(hPcomp c x hxc).trans hEq,hint⟩

end PoincareConjecture.M76
