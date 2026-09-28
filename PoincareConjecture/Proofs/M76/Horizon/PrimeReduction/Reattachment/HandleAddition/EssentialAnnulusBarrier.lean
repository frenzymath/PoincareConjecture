import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialAnnulusBarrierRetraction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialAnnulusBarrierDeformation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.EnclosingAnnularCircle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.EssentialAnnulusBallProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAnnularCarrier
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SquareCylinder

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Time" => unitInterval

theorem HamiltonMarkedProtectedBall.exists_enclosing_circle_boundary_deformation
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
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∃ K : C(Time × ↥(frontier E \ p '' P.boundary ℝ),frontier E),
      (∀ x : ↥(frontier E \ p '' P.boundary ℝ),
        (K (0,x) : LatticeHandleAmbient ι κ L) = x) ∧
      (∀ x, (K (1,x) : LatticeHandleAmbient ι κ L) ∈ E ∩ frontier R) ∧
      ∀ t (x : ↥(frontier E \ p '' P.boundary ℝ)),
        (x : LatticeHandleAmbient ι κ L) ∈ E ∩ frontier R →
        (K (t,x) : LatticeHandleAmbient ι κ L) = x := by
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
  have hh := exists_annulus_complement_deformation
    (isClosed_closure.inter isClosed_frontier) (hcAnn.image_of_continuousOn hp).isClosed
    W hcover hWrim
  dsimp only at hh
  rw [hcore] at hh
  exact hh

theorem HamiltonMarkedProtectedBall.old_exterior_boundary_outside_open_patch
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    {x : LatticeHandleAmbient ι κ L}
    (hx : x ∈ closure (latticeHandleDomain ι κ L \ D) ∩
      frontier (latticeHandleDomain ι κ L)) :
    x.2 ∉ (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      Metric.ball (0 : κ → ℝ) (3/2) := by
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hxf : x.1 ∈ sphere (0 : ι → ℝ) 1 := by
    have hf := hx.2
    change x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
      (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hf
    rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hf
    exact hf.1
  rintro ⟨z,hz,hzx⟩
  have hatt : x ∈ hamiltonAttachingBlock ι κ L (3/2) :=
    ⟨(x.1,z),⟨hxf,ball_subset_closedBall hz⟩,Prod.ext rfl hzx⟩
  have hxD := (hmark.symm.subset hatt).1
  have ht := (b.closed_complement_lateral_contact he hdim hi).subset ⟨hx.1,hxD⟩
  apply ht.2
  refine ⟨hatt,?_⟩
  rintro ⟨w,hw,hwx⟩
  have hh := b.quotient_injOn_attaching_disk (by omega)
    (sphere_subset_closedBall hw.2) (ball_subset_closedBall hz)
    ((congrArg Prod.snd hwx).trans hzx.symm)
  have hn := mem_sphere_zero_iff_norm.mp hw.2
  have hz' := mem_ball_zero_iff.mp hz
  rw [hh] at hn
  linarith

theorem HamiltonMarkedProtectedBall.essential_disk_meets_enclosing_annular_circle
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
    ∀ j : C(closedBall (0 : Fin 2 → ℝ) 1,E),
      (∀ z : sphere (0 : Fin 2 → ℝ) 1,
        (j ⟨z,sphere_subset_closedBall z.property⟩ : LatticeHandleAmbient ι κ L) ∈ frontier E) →
      (¬ ∃ F : C(closedBall (0 : Fin 2 → ℝ) 1,frontier E),
        ∀ z : sphere (0 : Fin 2 → ℝ) 1,
          (F ⟨z,sphere_subset_closedBall z.property⟩ : LatticeHandleAmbient ι κ L) =
            j ⟨z,sphere_subset_closedBall z.property⟩) →
      (range (fun z : sphere (0 : Fin 2 → ℝ) 1 =>
        (j ⟨z,sphere_subset_closedBall z.property⟩ : LatticeHandleAmbient ι κ L)) ∩
          p '' P.boundary ℝ).Nonempty := by
  classical
  intro E j hj hno
  by_contra hmiss
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let Q2 := sphere (0 : Fin 2 → ℝ) 1
  let D2 := closedBall (0 : Fin 2 → ℝ) 1
  let C := p '' P.boundary ℝ
  obtain ⟨K,h0,h1,_⟩ := b.exists_enclosing_circle_boundary_deformation
    he hdim hi p hp hpi hfront hfull hint hends P hP hPi hdepth hencl
  let rim : C(Q2,D2) := ⟨fun z => ⟨z,sphere_subset_closedBall z.property⟩,by fun_prop⟩
  let u : C(Q2,↥(frontier E \ C)) := ⟨fun z =>
    ⟨j (rim z),hj z,fun hz => hmiss ⟨j (rim z),mem_range_self z,hz⟩⟩,
    (continuous_subtype_val.comp (j.continuous.comp rim.continuous)).subtype_mk _⟩
  let f : C(Q2,frontier E) := ⟨fun z => ⟨j (rim z),hj z⟩,
    (continuous_subtype_val.comp (j.continuous.comp rim.continuous)).subtype_mk _⟩
  let g : C(Q2,frontier E) := K.comp ⟨fun z => (1,u z),by fun_prop⟩
  let H : f.Homotopy g := {
    toFun := fun z => K (z.1,u z.2)
    continuous_toFun := K.continuous.comp (continuous_fst.prodMk
      (u.continuous.comp continuous_snd))
    map_zero_left := fun z => Subtype.ext (h0 (u z))
    map_one_left := fun _ => rfl }
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  let S := sphere (0 : ι → ℝ) 1
  have hSf : S.Finite := by
    apply ((Set.finite_singleton (fun _ : ι => (-1 : ℝ))).insert (fun _ : ι => (1 : ℝ))).subset
    intro x hx
    have hc : x = (fun _ => x default) := funext (fun i => congrArg x (Subsingleton.elim i default))
    have hn : |x default| = 1 := by
      have hh := mem_sphere_zero_iff_norm.mp hx
      rwa [hc,pi_norm_const,Real.norm_eq_abs] at hh
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hn
    rcases hn with hn | hn
    · exact Or.inl (hc.trans (by rw [hn]))
    · exact Or.inr (hc.trans (by rw [hn]))
  let : Finite S := hSf.to_subtype
  let : DiscreteTopology S := inferInstance
  have hgS (z : Q2) : (g z : X).1 ∈ S := by
    have hh := (h1 (u z)).2
    change (g z : X) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
      (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hh
    rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hh
    exact hh.1
  let first : C(Q2,S) := ⟨fun z => ⟨(g z : X).1,hgS z⟩,by fun_prop⟩
  let : ConnectedSpace Q2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank];simp) (0 : Fin 2 → ℝ) zero_le_one)
  let : Nonempty Q2 := (NormedSpace.sphere_nonempty.mpr zero_le_one :
    (sphere (0 : Fin 2 → ℝ) 1).Nonempty).to_subtype
  let z0 : Q2 := Classical.choice inferInstance
  let a : S := first z0
  have hfirst (z : Q2) : first z = a :=
    (isPreconnected_range first.continuous).subsingleton (mem_range_self z) (mem_range_self z0)
  obtain ⟨r,_,_,hr⟩ := b.exists_exterior_old_boundary_projection he hdim hi a
  let inc : C(frontier E,E) := ⟨fun x => ⟨x,isClosed_closure.frontier_subset x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hfix (z : Q2) : r (inc (g z)) = g z := by
    apply Subtype.ext
    exact hr (inc (g z)) (congrArg Subtype.val (hfirst z))
      (b.old_exterior_boundary_outside_open_patch he hdim hi (h1 (u z)))
  obtain ⟨F,hF⟩ := exists_disk_extension_of_fixed_projection_homotopy
    inc r j f g ⟨H⟩ (fun _ => rfl) hfix
  exact hno ⟨F,fun z => congrArg Subtype.val (hF z)⟩

end PoincareConjecture.M76
