import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialAnnulusBarrier



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip unitInterval
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem HamiltonMarkedProtectedBall.exists_enclosing_circle_annular_coordinates
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : ContinuousOn p Ann) (hpi : InjOn p Ann)
    (hfront : p '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ p '' Ann)
    (hint : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (hends : ∀ z : Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ W : ((sphere (0 : Fin 2 → ℝ) 1) × Icc (-1 : ℝ) 1) ≃ₜ (p '' Ann),
      p '' Ann = E ∩ D ∧
      (∀ z, (W z : LatticeHandleAmbient ι κ L) ∈
        frontier (latticeHandleDomain ι κ L) ↔
          (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1) ∧
      (fun z => (W z : LatticeHandleAmbient ι κ L)) '' {z | (z.2 : ℝ) = 0} =
        p '' P.boundary ℝ := by
  classical
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  let A := E ∩ frontier R
  let T := p '' Ann
  have hcAnn : IsCompact Ann :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_Ioo.prod isOpen_Ioo)
  have hT : T = E ∩ D :=
    (marked_annular_image_eq_frontier_closure p hp hfront hfull hint hends).trans
      (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
        b.ball.closure_interior).symm
  obtain ⟨_,_,_,hcontact,_,_,hfrontE⟩ := b.closed_complement_geometry he hdim hi
  have hcover : A ∪ T = frontier E := by
    rw [hfrontE,←hcontact,←hT]
    exact union_comm _ _
  let f : Ann → T := fun z => ⟨p z,z,z.property,rfl⟩
  have hf : Continuous f := hp.domRestrict.subtype_mk _
  have hfi : Function.Injective f := fun x y h =>
    Subtype.ext (hpi x.property y.property (congrArg Subtype.val h))
  have hfs : Function.Surjective f := by
    rintro ⟨x,z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,rfl⟩
  let : CompactSpace Ann := isCompact_iff_compactSpace.mp hcAnn
  let H := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs
  obtain ⟨gamma,a,hgi,ha,hav,hgd,hgr,_,hge⟩ :=
    exists_essential_enclosing_annular_circle P hP hPi hdepth hencl
  obtain ⟨G,_,_,hfix,hrange,_⟩ :=
    Dehn.exists_finitePL_annular_straightening gamma hgi a ha hav hgd hge
  have hGfix (z : Ann) (hz : depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :
      G z = z := by
    rcases hz with hz | hz
    · obtain ⟨w,rfl⟩ := (Dehn.range_annulusRimPoint false).symm.subset hz
      exact hfix false w
    · obtain ⟨w,rfl⟩ := (Dehn.range_annulusRimPoint true).symm.subset hz
      exact hfix true w
  have hGends (z : Ann) :
      (depth 8 (G.symm z : P2) = -1 ∨ depth 8 (G.symm z : P2) = 1) ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 := by
    constructor
    · intro hz
      have hh := hGfix (G.symm z) hz
      rw [G.apply_symm_apply] at hh
      exact hh ▸ hz
    · intro hz
      have hh : G.symm z = z := by
        apply G.injective
        rw [G.apply_symm_apply,hGfix z hz]
      simpa only [hh] using hz
  obtain ⟨C,_,hCv⟩ := Dehn.Annuli.exists_selected_annulus_cylinder
  let CY := sphere (0 : Fin 2 → ℝ) 1
  let J := Icc (-1 : ℝ) 1
  let W : (CY × J) ≃ₜ T :=
    (Homeomorph.Set.prod CY J).symm.trans (C.symm.trans (G.symm.trans H))
  have hWrim (z : CY × J) : (W z : X) ∈ A ↔
      (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 := by
    have hWE : (W z : X) ∈ E := (hT.subset (W z).property).1
    change ((p (G.symm (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩))) ∈ E ∧
      p (G.symm (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)) ∈ frontier R) ↔ _
    change p (G.symm (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)) ∈ E at hWE
    rw [and_iff_right hWE,hends,hGends]
    have hh := hCv (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)
    rw [C.apply_symm_apply] at hh
    rw [←hh]
  have hcore : (fun z => (W z : X)) '' {z : CY × J | (z.2 : ℝ) = 0} =
      p '' P.boundary ℝ := by
    have hGimage : G.symm '' {z : Ann | depth 8 (z : P2) = 0} = range gamma := by
      rw [←range_annulus_core_depth_zero,←hrange,image_image]
      simp only [G.symm_apply_apply,image_id']
    have hCimage : (fun z : CY × J => C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩) ''
        {z | (z.2 : ℝ) = 0} = {z : Ann | depth 8 (z : P2) = 0} := by
      ext w
      constructor
      · rintro ⟨z,hz,rfl⟩
        have hh := hCv (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)
        rw [C.apply_symm_apply] at hh
        exact hh.symm.trans hz
      · intro hw
        let z : CY × J := (⟨(C w).val.1,(C w).property.1⟩,⟨(C w).val.2,(C w).property.2⟩)
        refine ⟨z,(hCv w).trans hw,?_⟩
        exact C.symm_apply_apply w
    change ((p ∘ Subtype.val) ∘ G.symm ∘
      (fun z : CY × J => C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)) '' _ = _
    simp only [image_comp]
    rw [hCimage,hGimage,hgr]
  refine ⟨W,hT,?_,hcore⟩
  intro z
  have hWE : (W z : X) ∈ E := (hT.subset (W z).property).1
  exact (and_iff_right hWE).symm.trans (hWrim z)

theorem exists_closed_half_cylinder
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y]
    {T F : Set X} (W : (Y × Icc (-1 : ℝ) 1) ≃ₜ T)
    (hends : ∀ z, (W z : X) ∈ F ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
    (side : Bool) :
    ∃ B : Set X, IsClosed B ∧ B ⊆ T ∧
      ∃ H : (Y × I) ≃ₜ B,
        (∀ z, (H z : X) ∈ F ↔ (z.2 : ℝ) = 0) ∧
        (range (fun y => (H (y,1) : X)) =
          (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0}) ∧
        ∀ z, ∃ w, w.1 = z.1 ∧
          (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
          (H z : X) = W w := by
  let height : I → ℝ := fun t => if side then 1 - t else t - 1
  have hh (t : I) : height t ∈ Icc (-1 : ℝ) 1 := by
    have ht0 := t.property.1
    have ht1 := t.property.2
    cases side <;> simp only [height,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith
  let j : Y × I → Y × Icc (-1 : ℝ) 1 := fun z => (z.1,⟨height z.2,hh z.2⟩)
  have hjc : Continuous j := by
    apply continuous_fst.prodMk
    apply Continuous.subtype_mk
    cases side <;> dsimp [height] <;> fun_prop
  have hji : Function.Injective j := by
    intro z w heq
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg (fun x : Y × Icc (-1 : ℝ) 1 => (x.2 : ℝ)) heq
    change z.1 = w.1 at hfst
    apply Prod.ext hfst
    apply Subtype.ext
    change height z.2 = height w.2 at hsnd
    cases side <;> dsimp [height] at hsnd <;> linarith
  let f : Y × I → X := fun z => W (j z)
  have hfc : Continuous f := continuous_subtype_val.comp (W.continuous.comp hjc)
  have hfi : Function.Injective f := fun z w h => hji (W.injective (Subtype.ext h))
  let B := range f
  let fB : Y × I → B := fun z => ⟨f z,mem_range_self z⟩
  have hfBc : Continuous fB := hfc.subtype_mk _
  have hfBi : Function.Injective fB := fun z w h =>
    hfi (congrArg (fun x : B => (x : X)) h)
  have hfBs : Function.Surjective fB := by
    rintro ⟨_,z,rfl⟩
    exact ⟨z,rfl⟩
  let H := (hfBc.isClosedEmbedding hfBi).isEmbedding.toHomeomorphOfSurjective hfBs
  refine ⟨B,(isCompact_range hfc).isClosed,?_,H,?_,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    exact (W (j z)).property
  · intro z
    change f z ∈ F ↔ _
    rw [hends]
    change height z.2 = -1 ∨ height z.2 = 1 ↔ (z.2 : ℝ) = 0
    have ht0 := z.2.property.1
    have ht1 := z.2.property.2
    cases side <;> dsimp [height] <;> constructor
    · rintro (h | h) <;> linarith
    · intro h; left; linarith
    · rintro (h | h) <;> linarith
    · intro h; right; linarith
  · have hj1 (y : Y) : j (y,1) = (y,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        cases side <;> norm_num [j,height]
    apply Subset.antisymm
    · rintro _ ⟨y,rfl⟩
      refine ⟨j (y,1),?_,rfl⟩
      rw [hj1]
      rfl
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨z.1,?_⟩
      change (W (j (z.1,1)) : X) = W z
      rw [hj1]
      have hh : ((z.1,⟨0,by norm_num⟩) : Y × Icc (-1 : ℝ) 1) = z :=
        Prod.ext rfl (Subtype.ext hz.symm)
      rw [hh]
  · intro z
    exact ⟨j z,rfl,rfl,rfl⟩

end PoincareConjecture.M76

