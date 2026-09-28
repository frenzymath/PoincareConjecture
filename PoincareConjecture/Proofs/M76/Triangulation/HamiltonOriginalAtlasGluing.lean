import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.ImmersionPLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLChartRestriction












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem pl_transition_mem_of_overlap_cover
    {X ι : Type*} [TopologicalSpace X]
    (c : ι → OpenPartialHomeomorph X V3)
    (e f : OpenPartialHomeomorph X V3)
    (hcover : ∀ x ∈ e.source ∩ f.source, ∃ i, x ∈ (c i).source)
    (hce : ∀ i, (c i).symm.trans e ∈ piecewiseAffineGroupoid V3)
    (hcf : ∀ i, (c i).symm.trans f ∈ piecewiseAffineGroupoid V3) :
    e.symm.trans f ∈ piecewiseAffineGroupoid V3 := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨i, hi⟩ := hcover (e.symm x) ⟨e.map_target hx.1, hx.2⟩
  let U := (e.symm.trans (c i)).source
  have hxU : x ∈ U := ⟨hx.1, hi⟩
  have hei : e.symm.trans (c i) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hce i)
  have hcomp := ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcf i)).comp
    ((mem_piecewiseAffineGroupoid_iff_forward _).mp hei)
  refine ⟨U, hxU, ?_⟩
  have hsub : (e.symm.trans f).source ∩ U ⊆
      (e.symm.trans (c i)).source ∩
        (e.symm.trans (c i)) ⁻¹' ((c i).symm.trans f).source := by
    intro y hy
    refine ⟨hy.2, (c i).map_source hy.2.2, ?_⟩
    change (c i).symm (c i (e.symm y)) ∈ f.source
    have hyi : e.symm y ∈ (c i).source := hy.2.2
    rw [(c i).left_inv hyi]
    exact hy.1.2
  apply (hcomp.mono ((e.symm.trans f).open_source.inter
    (e.symm.trans (c i)).open_source) hsub).congr
  intro y hy
  change f ((c i).symm (c i (e.symm y))) = f (e.symm y)
  have hyi : e.symm y ∈ (c i).source := hy.2.2
  rw [(c i).left_inv hyi]







theorem exists_original_immersion_collar_PL_domain
    {X ι : Type*} [TopologicalSpace X]
    (d : ι → OpenPartialHomeomorph X V3) {R A B : Set X}
    (hd : PLDomain d R) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) (hboundary : frontier R ⊆ B)
    (f : X → V3) (hf : IsLocalHomeomorphOn f A)
    (hPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (d i).symm)
      ((d i).target ∩ (d i).symm ⁻¹' (A ∩ B))) :
    ∃ charts : Set (OpenPartialHomeomorph X V3),
      PLDomain (fun c : charts => (c : OpenPartialHomeomorph X V3)) R ∧
      (∀ e : OpenPartialHomeomorph X V3,
        e.source ⊆ A → EqOn e f e.source → e ∈ charts) ∧
      (∀ i, (d i).restr B ∈ charts) ∧
      ∀ (e : charts) i,
        ((d i).restr B).symm.trans (e : OpenPartialHomeomorph X V3) ∈
          piecewiseAffineGroupoid V3 := by
  classical
  let original : Set (OpenPartialHomeomorph X V3) :=
    {e | e.source ⊆ A ∧ EqOn e f e.source}
  let charts := original ∪ range (fun i => (d i).restr B)
  have hcross (e : OpenPartialHomeomorph X V3) (he : e ∈ charts) (i : ι) :
      ((d i).restr B).symm.trans e ∈ piecewiseAffineGroupoid V3 := by
    rcases he with he | ⟨j, rfl⟩
    · apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      have hsub : (((d i).restr B).symm.trans e).source ⊆
          (d i).target ∩ (d i).symm ⁻¹' (A ∩ B) := by
        intro x hx
        exact ⟨hx.1.1, he.1 hx.2, interior_subset hx.1.2⟩
      apply ((hPL i).mono (((d i).restr B).symm.trans e).open_source hsub).congr
      intro x hx
      exact (he.2 hx.2).symm
    · exact (d i).restricted_transition_mem_piecewiseAffineGroupoid
        (d j) (hd.compatible i j) B B
  have hcompat (e g : OpenPartialHomeomorph X V3)
      (he : e ∈ charts) (hg : g ∈ charts) :
      e.symm.trans g ∈ piecewiseAffineGroupoid V3 := by
    rcases he with he | ⟨i, rfl⟩
    · rcases hg with hg | ⟨j, rfl⟩
      · apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
        apply (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3)
          (e.symm.trans g).open_source).congr
        intro x hx
        change x = g (e.symm x)
        have hxg : e.symm x ∈ g.source := hx.2
        have hxe : e.symm x ∈ e.source := e.map_target hx.1
        rw [hg.2 hxg, ← he.2 hxe]
        exact (e.right_inv hx.1).symm
      · have hp := (piecewiseAffineGroupoid V3).symm (hcross e (Or.inl he) j)
        simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm] using hp
    · exact hcross g hg i
  refine ⟨charts, ⟨?_, fun e g => hcompat e g e.property g.property, hd.closed, ?_⟩,
    fun e hsource heq => Or.inl ⟨hsource, heq⟩,
    fun i => Or.inr ⟨i, rfl⟩, fun e i => hcross e e.property i⟩
  · intro x
    have hx : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · obtain ⟨e, hxe, he⟩ := hf x hx
      let c := e.restr A
      have hcs : c.source ⊆ A := fun _ hy => interior_subset hy.2
      have hce : EqOn c f c.source := by
        intro y _
        exact congrFun he.symm y
      refine ⟨⟨c, Or.inl ⟨hcs, hce⟩⟩, ?_⟩
      rw [OpenPartialHomeomorph.restr_source' _ _ hA]
      exact ⟨hxe, hx⟩
    · obtain ⟨i, hi⟩ := hd.cover x
      refine ⟨⟨(d i).restr B, Or.inr ⟨i, rfl⟩⟩, ?_⟩
      rw [OpenPartialHomeomorph.restr_source' _ _ hB]
      exact ⟨hi, hx⟩
  · intro x hx
    obtain ⟨ell, v, H, hv, hxH, hzero, hH, hhalf⟩ := hd.halfspace x hx
    refine ⟨ell, v, H.restr B, hv, ?_, hzero, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.restr_source' _ _ hB]
      exact ⟨hxH, hboundary hx⟩
    · intro e
      apply pl_transition_mem_of_overlap_cover (fun i => (d i).restr B)
      · intro y hy
        obtain ⟨i, hi⟩ := hd.cover y
        refine ⟨i, ?_⟩
        rw [OpenPartialHomeomorph.restr_source' _ _ hB]
        exact ⟨hi, interior_subset hy.2.2⟩
      · exact fun i => hcross e e.property i
      · exact fun i => (d i).restricted_transition_mem_piecewiseAffineGroupoid
          H (hH i) B B
    · intro y hy
      exact hhalf y hy.1

end PoincareConjecture.M76
