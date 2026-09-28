import PoincareConjecture.Proofs.M76.Rigidity.StandardMeridian
import PoincareConjecture.Proofs.M76.Rigidity.MarkedMaps
import PoincareConjecture.Proofs.M76.Rigidity.BoundaryInverseCoordinates

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_finite_hamiltonMeridianRim :
    ∃ K : SimplicialComplex ℝ V2, K.faces.Finite ∧ K.space = Q := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2))
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := he
  refine ⟨K.frontierSubcomplex D, K.frontierSubcomplex_finite D hK, ?_⟩
  rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
    frontier_closedBall _ one_ne_zero]

variable (L : Submodule ℤ (Fin 1 → ℝ))

theorem StandardLatticeHandleAtlas.polyhedralPL_standardMeridianRim
    {β : Type*}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d (hamiltonStandardMeridianMap L) Q := by
  obtain ⟨K, hK, hKQ⟩ := exists_finite_hamiltonMeridianRim
  have hKD : K.space ⊆ D := hKQ.subset.trans sphere_subset_closedBall
  have h := (hd.polyhedralPL_standardMeridian L).restrict_finite K hK hKD
  rwa [hKQ] at h

theorem isEmbedding_hamiltonMeridianRim :
    Topology.IsEmbedding (fun x : Q => hamiltonStandardMeridianMap L x) :=
  (isEmbedding_prodMkLeft 0).comp Topology.IsEmbedding.subtypeVal

theorem polyhedralPL_source_hamiltonMeridianRim
    {α β : Type*}
    {e : α → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(LatticeHandle (Fin 2) (Fin 1) L, LatticeHandle (Fin 2) (Fin 1) L))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id (LatticeHandle (Fin 2) (Fin 1) L)).HomotopyRel phi
      (latticeHandleBoundary (Fin 2) (Fin 1) L)) :
    PolyhedralPLInCharts e (hamiltonStandardMeridianMap L) Q := by
  classical
  let R := latticeHandleDomain (Fin 2) (Fin 1) L
  let f := latticeHandleMapInDomain (Fin 2) (Fin 1) L phi
  let F' := latticeHandleMapInDomain_homotopyRel (Fin 2) (Fin 1) L phi F
  let q : V2 → R := fun x => if hx : x ∈ D then
    ⟨(x, 0), hx, mem_univ _⟩ else
      ⟨(0, 0), mem_closedBall_self zero_le_one, mem_univ _⟩
  have hqval (x : V2) (hx : x ∈ Q) :
      (q x : LatticeHandleAmbient (Fin 2) (Fin 1) L) =
        hamiltonStandardMeridianMap L x := by
    simp only [q, dif_pos (sphere_subset_closedBall hx)]
    rfl
  have hq : ContinuousOn q Q :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      ((continuous_id.prodMk continuous_const).continuousOn.congr hqval)
  have hqB : MapsTo q Q
      ((Subtype.val : R → LatticeHandleAmbient (Fin 2) (Fin 1) L) ⁻¹' frontier R) := by
    intro x hx
    change (q x : LatticeHandleAmbient (Fin 2) (Fin 1) L) ∈ frontier R
    rw [hqval x hx]
    change (x, 0) ∈ frontier (latticeHandleDomain (Fin 2) (Fin 1) L)
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hx, mem_univ _⟩
  have hfi : InjOn f
      ((Subtype.val : R → LatticeHandleAmbient (Fin 2) (Fin 1) L) ⁻¹' frontier R) := by
    intro x hx y hy heq
    exact (F'.fst_eq_snd hx).trans (heq.trans (F'.fst_eq_snd hy).symm)
  have hfq : PolyhedralPLInCharts d
      (fun x => (f (q x) : LatticeHandleAmbient (Fin 2) (Fin 1) L)) Q :=
    (hd.polyhedralPL_standardMeridianRim L).congr (fun x hx =>
      (hqval x hx).symm.trans (congrArg Subtype.val (F'.fst_eq_snd (hqB hx))))
  obtain ⟨K, hK, hKQ⟩ := exists_finite_hamiltonMeridianRim
  have hqK : ContinuousOn q K.space := hKQ.symm ▸ hq
  have hqBK : MapsTo q K.space
      ((Subtype.val : R → LatticeHandleAmbient (Fin 2) (Fin 1) L) ⁻¹' frontier R) :=
    hKQ.symm ▸ hqB
  have hfqK : PolyhedralPLInCharts d
      (fun x => (f (q x) : LatticeHandleAmbient (Fin 2) (Fin 1) L)) K.space :=
    hKQ.symm ▸ hfq
  have hsource := hphi.polyhedralPLInCharts_boundary_lift hfi K hK q hqK hqBK hfqK
  rw [hKQ] at hsource
  exact hsource.congr hqval

end PoincareConjecture.M76
