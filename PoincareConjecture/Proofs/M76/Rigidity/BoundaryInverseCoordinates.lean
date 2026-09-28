import PoincareConjecture.Proofs.M76.Rigidity.BoundaryPatch
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X Y G ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {e : ι → OpenPartialHomeomorph X V3}
  {d : κ → OpenPartialHomeomorph Y V3} {R : Set X} {T : Set Y}

theorem ChartwisePLMap.polyhedralPLInCharts_boundary_lift
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (hfi : InjOn f ((Subtype.val : R → X) ⁻¹' frontier R))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (q : G → R) (hq : ContinuousOn q K.space)
    (hqB : MapsTo q K.space ((Subtype.val : R → X) ⁻¹' frontier R))
    (hfq : PolyhedralPLInCharts d (fun z => (f (q z) : Y)) K.space) :
    PolyhedralPLInCharts e (fun z => (q z : X)) K.space := by
  classical
  have hqc : ContinuousOn (fun z => (q z : X)) K.space :=
    continuous_subtype_val.comp_continuousOn hq
  refine ⟨hqc, ?_⟩
  intro x
  obtain ⟨B, J, V, hJ, hV, hqxV, hVB, hJt, hJfront, hVJ, hBPL, hBcompat⟩ :=
    hf.source_domain.exists_polyhedral_boundary_patch (hqB x.property)
  let r : V3 → R := fun z =>
    if hz : B.symm z ∈ R then ⟨B.symm z, hz⟩ else q x
  have hrval (z : V3) (hz : z ∈ J.space) : (r z : X) = B.symm z := by
    have hzR : B.symm z ∈ R :=
      hf.source_domain.closed.closure_subset (frontier_subset_closure (hJfront hz))
    simp only [r, dif_pos hzR]
  have hrB (z : V3) (hz : z ∈ J.space) :
      r z ∈ (Subtype.val : R → X) ⁻¹' frontier R := by
    change (r z : X) ∈ frontier R
    rw [hrval z hz]
    exact hJfront hz
  have hr : ContinuousOn r J.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      ((B.symm.continuousOn.mono hJt).congr hrval)
  have hre : PolyhedralPLInCharts e (fun z => (r z : X)) J.space :=
    hBPL.congr (fun z hz => (hrval z hz).symm)
  have hfr : PolyhedralPLInCharts d (fun z => (f (r z) : Y)) J.space :=
    hf.polyhedralPLInCharts_comp J hJ r hr hre (fun _ _ => mem_univ _)
  have hfrinj : InjOn (fun z => (f (r z) : Y)) J.space := by
    intro z hz w hw heq
    have hrw : r z = r w := hfi (hrB z hz) (hrB w hw) (Subtype.ext heq)
    have hbw : B.symm z = B.symm w :=
      (hrval z hz).symm.trans ((congrArg Subtype.val hrw).trans (hrval w hw))
    exact B.symm.injOn (hJt hz) (hJt hw) hbw
  obtain ⟨i, hqxi⟩ := hf.source_domain.cover (q x)
  let O : Set K.space := (fun y => (q y : X)) ⁻¹' (V ∩ (e i).source)
  have hO : IsOpen O := (hV.inter (e i).open_source).preimage hqc.domRestrict
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hqxV, hqxi⟩
  have hqV (y : G) (hy : y ∈ N.space) : (q y : X) ∈ V :=
    (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1
  have hqi (y : G) (hy : y ∈ N.space) : (q y : X) ∈ (e i).source :=
    (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2
  have hqBchart (y : G) (hy : y ∈ N.space) : (q y : X) ∈ B.source :=
    hVB (hqV y hy)
  have hqJ : MapsTo (fun y => B (q y)) N.space J.space := by
    intro y hy
    exact hVJ (q y) (hqV y hy) (hqB (hNK hy))
  have hrq (y : G) (hy : y ∈ N.space) : r (B (q y)) = q y := by
    apply Subtype.ext
    rw [hrval _ (hqJ hy), B.left_inv (hqBchart y hy)]
  have hqBcont : ContinuousOn (fun y => B (q y)) N.space :=
    B.continuousOn.comp (hqc.mono hNK) (fun y hy => hqBchart y hy)
  have hfrq : PolyhedralPLInCharts d
      ((fun z => (f (r z) : Y)) ∘ (fun y => B (q y))) N.space :=
    (hfq.restrict_finite N hN hNK).congr (fun y hy => by
      change (f (q y) : Y) = (f (r (B (q y))) : Y)
      rw [hrq y hy])
  have hqcoords : FinitePiecewiseAffineOn (fun y => B (q y)) N.space :=
    hfr.finitePiecewiseAffineOn_lift hf.target_domain.compatible
      hfrinj N hN hqBcont hqJ hfrq
  have hchange := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (hBcompat i)).1
  have hchanged := hchange.comp_finitePiecewiseAffineOn hqcoords (by
    intro y hy
    change B (q y) ∈ B.target ∧ B.symm (B (q y)) ∈ (e i).source
    refine ⟨B.map_source (hqBchart y hy), ?_⟩
    rw [B.left_inv (hqBchart y hy)]
    exact hqi y hy)
  have hfinal : FinitePiecewiseAffineOn (fun y => e i (q y)) N.space :=
    hchanged.congr (fun y hy => by
      change e i (B.symm (B (q y))) = e i (q y)
      rw [B.left_inv (hqBchart y hy)])
  exact ⟨i, N, W, hN, hNK, hW, hxW, hWN, fun y hy => hqi y hy, hfinal⟩

end PoincareConjecture.M76
