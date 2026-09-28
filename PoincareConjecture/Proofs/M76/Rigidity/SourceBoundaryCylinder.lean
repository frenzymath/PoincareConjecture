import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianRim
import PoincareConjecture.Proofs.M76.Rigidity.MeridianCut

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLMap.polyhedralPLInCharts_boundary_fixed
    {X G ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph X V3} {R : Set X}
    {f : C(R, R)} (hf : ChartwisePLMap e d f)
    (hfix : ∀ x : R, (x : X) ∈ frontier R → f x = x)
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (q : G → R) (hq : ContinuousOn q K.space)
    (hqB : MapsTo q K.space ((Subtype.val : R → X) ⁻¹' frontier R))
    (hqPL : PolyhedralPLInCharts d (fun z => (q z : X)) K.space) :
    PolyhedralPLInCharts e (fun z => (q z : X)) K.space := by
  have hfi : InjOn f ((Subtype.val : R → X) ⁻¹' frontier R) := by
    intro x hx y hy heq
    exact (hfix x hx).symm.trans (heq.trans (hfix y hy))
  have hfq : PolyhedralPLInCharts d (fun z => (f (q z) : X)) K.space :=
    hqPL.congr (fun z hz => (congrArg Subtype.val (hfix (q z) (hqB hz))).symm)
  exact hf.polyhedralPLInCharts_boundary_lift hfi K hK q hq hqB hfq

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

theorem exists_finite_hamiltonBoundaryCylinder :
    ∃ K : SimplicialComplex ℝ (V2 × ℝ),
      K.faces.Finite ∧ K.space = Q ×ˢ Icc (0 : ℝ) p := by
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_hamiltonMeridianRim
  obtain ⟨_, _, _, _, _, b, hb, _⟩ :=
    (isFinitePLBallPair_Icc (a := (0 : ℝ)) (b := p) (by norm_num))
  obtain ⟨_, ⟨C, hC, hCp, _⟩, _⟩ := hb
  obtain ⟨K, hK, hKspace, _⟩ := J.exists_finite_triangulation_prod C hJ hC
  refine ⟨K, hK, ?_⟩
  rw [hKspace, hJQ, hCp]

theorem StandardLatticeHandleAtlas.polyhedralPL_boundaryCylinder
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d hamiltonMeridianCutAmbientMap (Q ×ˢ Icc (0 : ℝ) p) := by
  obtain ⟨K, hK, hKA⟩ := exists_finite_hamiltonBoundaryCylinder
  have hKcut : K.space ⊆ D ×ˢ Icc (0 : ℝ) p :=
    hKA.subset.trans (prod_mono sphere_subset_closedBall subset_rfl)
  have h := hd.polyhedralPL_meridianCut.restrict_finite K hK hKcut
  rwa [hKA] at h

theorem polyhedralPL_source_hamiltonBoundaryCylinder
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap (Q ×ˢ Icc (0 : ℝ) p) := by
  classical
  let R := latticeHandleDomain (Fin 2) (Fin 1) L
  let f := latticeHandleMapInDomain (Fin 2) (Fin 1) L phi
  let F' := latticeHandleMapInDomain_homotopyRel (Fin 2) (Fin 1) L phi F
  let q : (V2 × ℝ) → R := fun z => if hz : z.1 ∈ D then
    ⟨hamiltonMeridianCutAmbientMap z, hz, mem_univ _⟩ else
      ⟨(0, 0), mem_closedBall_self zero_le_one, mem_univ _⟩
  have hqval (z : V2 × ℝ) (hz : z ∈ Q ×ˢ Icc (0 : ℝ) p) :
      (q z : X) = hamiltonMeridianCutAmbientMap z := by
    simp only [q, dif_pos (sphere_subset_closedBall hz.1)]
  have hc : Continuous hamiltonMeridianCutAmbientMap :=
    continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp
      (continuous_pi fun _ : Fin 1 => continuous_snd))
  have hq : ContinuousOn q (Q ×ˢ Icc (0 : ℝ) p) :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (hc.continuousOn.congr hqval)
  have hqB : MapsTo q (Q ×ˢ Icc (0 : ℝ) p)
      ((Subtype.val : R → X) ⁻¹' frontier R) := by
    intro z hz
    change (q z : X) ∈ frontier R
    rw [hqval z hz]
    change (z.1, QuotientAddGroup.mk (fun _ : Fin 1 => z.2)) ∈
      frontier (latticeHandleDomain (Fin 2) (Fin 1) L)
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hz.1, mem_univ _⟩
  have hfix (x : R) (hx : (x : X) ∈ frontier R) : f x = x :=
    (F'.fst_eq_snd hx).symm
  have hqPL : PolyhedralPLInCharts d (fun z => (q z : X)) (Q ×ˢ Icc (0 : ℝ) p) :=
    hd.polyhedralPL_boundaryCylinder.congr (fun z hz => (hqval z hz).symm)
  obtain ⟨K, hK, hKA⟩ := exists_finite_hamiltonBoundaryCylinder
  have hqK : ContinuousOn q K.space := hKA.symm ▸ hq
  have hqBK : MapsTo q K.space ((Subtype.val : R → X) ⁻¹' frontier R) :=
    hKA.symm ▸ hqB
  have hqPLK : PolyhedralPLInCharts d (fun z => (q z : X)) K.space :=
    hKA.symm ▸ hqPL
  have hsource := hphi.polyhedralPLInCharts_boundary_fixed hfix K hK q hqK hqBK hqPLK
  rw [hKA] at hsource
  exact hsource.congr hqval

end PoincareConjecture.M76
