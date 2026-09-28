import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalEnclosingArcEnd
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcRadialRetraction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcPolygonRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEndTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalEndFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalLabeledEndEmbedding








set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_terminal_polygon_region_with_core_exclusion
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
        (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    {A U C : Set P2} {f : P2 → LatticeHandleAmbient ι κ L}
    {u0 u1 c d : P2} (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {u0,u1}) (hC : IsFinitePLBallPair ℝ C {u0,u1})
    (hUC : U ∩ C = {u0,u1}) (hu : u0 ≠ u1)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hS : f '' A ∩ S = f '' C)
    (hF : f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U)
    (hPS : p '' P.boundary ℝ ⊆ S)
    (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ) (hcd : c ≠ d)
    (h0 : f u0 = p c) (h1 : f u1 = p d)
    (hinter : f '' U ∩ p '' P.boundary ℝ = {f u0,f u1}) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ O : Set (frontier E), IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
        closure O ≠ univ ∧
        ((Subtype.val : frontier E → LatticeHandleAmbient ι κ L) '' frontier O =
            f '' U ∪ p '' V ∨
         (Subtype.val : frontier E → LatticeHandleAmbient ι κ L) '' frontier O =
            f '' U ∪ p '' W) ∧
        Disjoint (Subtype.val '' O) (p '' P.boundary ℝ) ∧
        ∀ j : C(closedBall (0 : Fin 2 → ℝ) 1,frontier E),
          Function.Injective j → range j ⊆ closure O →
          ∀ (m : ℕ) (Q : Polygon P2 (m+3)), Q.HasSimplicialEdges →
            Function.Injective Q →
            (∀ x ∈ Q.boundary ℝ,-1 < depth 8 x ∧ depth 8 x < 1) →
            Dehn.annulusSquare 8 1 ⊆ Q.inside →
            ¬p '' Q.boundary ℝ ⊆ Subtype.val '' range j := by
  classical
  intro E
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hCA : C ⊆ A := subset_union_right.trans hA.1
  have hUrim : IsFinitePLBallPair ℝ U (U ∩ C) := hUC.symm ▸ hU
  obtain ⟨Wc,hWe,hWcore,a,ha,hal,side,hdata⟩ :=
    b.exists_original_enclosing_arc_end he hdim hi p hp hpi hfront hfull hint hends
      P hP hPi hdepth hencl hPS hA hUrim hf hfi hS hF
  let B := (fun z => (Wc z : X)) ''
    {z : CY × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
  let Old := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side}
  let End := Old ∪ B
  change IsCompact End ∧ _ at hdata
  obtain ⟨hEnd,hUE,hPE,F,hFi,hFO,hFhom,H,hHcore,hHcoords,v,hvi,hvn,hFB,hFrange⟩ := hdata
  have hPAnn : P.boundary ℝ ⊆ Ann := fun z hz =>
    mem_squareAnnulus_iff_depth.mpr ⟨(hdepth z hz).1.le,(hdepth z hz).2.le⟩
  let q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup) := ⟨Prod.snd,continuous_snd⟩
  obtain ⟨V,W,hV,hW,hVW,hVWint,O,ho,hko,hsco,hfrontO,hdisO⟩ :=
    s.exists_selected_terminal_polygon_region_with_core_avoidance L (by omega)
      hA hf hfi hCA hC.isConnected hS q hEnd F hFi hFhom hFrange H subset_union_right
      v hvn hFB hU hu hUA hUE P hP hPi hc hd hcd (hp.mono hPAnn) (hpi.mono hPAnn)
      h0 h1 hinter hPS hHcore
  have hcover : (E ∩ frontier R) ∪ (E ∩ D) = frontier E := by
    obtain ⟨_,_,_,hcontact,_,_,hfr⟩ := b.closed_complement_geometry he hdim hi
    rw [hfr,←hcontact]
    exact union_comm _ _
  have hEndF : End ⊆ frontier E := by
    rintro x (hx | ⟨z,_,rfl⟩)
    · exact hcover.subset (Or.inl hx.1)
    · exact hcover.subset (Or.inr (Wc z).property)
  let inc : End → frontier E := fun x => ⟨x,hEndF x.property⟩
  let : CompactSpace End := isCompact_iff_compactSpace.mp hEnd
  have hic : Continuous inc := continuous_subtype_val.subtype_mk _
  have hii : Function.Injective inc := fun x y hh =>
    Subtype.ext (congrArg (fun z : frontier E => (z : X)) hh)
  have hiemb := hic.isClosedEmbedding hii
  have hrange : range inc = (Subtype.val ⁻¹' End : Set (frontier E)) := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact z.property
    · intro hx; exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩
  have htop := b.original_labeled_end_frontier he hdim hi Wc hWe a ha hal side
  have hintO : inc '' O ⊆ interior (range inc) := by
    rw [hrange,htop.1]
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨z.property,?_⟩
    intro hcorez
    exact disjoint_left.mp hdisO (mem_image_of_mem Subtype.val hz) (hWcore.subset hcorez)
  obtain ⟨ho',hko',hsco',hcl',hfront'⟩ :=
    region_image_in_range_interior hiemb ho hko hsco hintO
  have hproper : closure (inc '' O) ≠ univ := by
    intro hall
    have hsub : closure (inc '' O) ⊆ range inc := by
      rw [hcl']
      exact image_subset_range _ _
    have hrall : range inc = univ := eq_univ_of_subset hsub hall
    have hfrEmpty : frontier (Subtype.val ⁻¹' End : Set (frontier E)) = ∅ := by
      rw [←hrange,hrall,frontier_univ]
    have hcoreEmpty := htop.2.1.symm.trans hfrEmpty
    obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr zero_le_one :
      (sphere (0 : Fin 2 → ℝ) 1).Nonempty)
    let z : CY := ⟨y,hy⟩
    have hzE : (H (z,1) : X) ∈ End := Or.inr (H (z,1)).property
    have hzC := hWcore.symm.subset (hHcore.subset (mem_range_self z))
    exact (hcoreEmpty.subset
      (show (⟨H (z,1),hEndF hzE⟩ : frontier E) ∈ Subtype.val ⁻¹'
        ((fun z => (Wc z : X)) '' {z | (z.2 : ℝ) = 0}) from hzC))
  refine ⟨V,W,hV,hW,hVW,hVWint,inc '' O,ho',hko',hsco',hproper,?_,?_,?_⟩
  · rw [hfront',image_image]
    exact hfrontO
  · apply disjoint_left.mpr
    rintro x ⟨_,⟨z,hz,rfl⟩,rfl⟩ hx
    exact disjoint_left.mp hdisO (mem_image_of_mem Subtype.val hz) hx

  · intro j hji hjO m Q hQ hQi hQdepth hQencl hQj
    have hjEnd (z : closedBall (0 : Fin 2 → ℝ) 1) : (j z : X) ∈ End := by
      have hh := hjO (mem_range_self z)
      rw [hcl'] at hh
      obtain ⟨y,hy,hyy⟩ := hh
      exact (congrArg (fun w : frontier E => (w : X)) hyy) ▸ y.property
    let jE : C(closedBall (0 : Fin 2 → ℝ) 1,End) :=
      ⟨fun z => ⟨j z,hjEnd z⟩,(continuous_subtype_val.comp j.continuous).subtype_mk _⟩
    have hjiE : Function.Injective jE := fun z w hh =>
      hji (Subtype.ext (congrArg (fun x : End => (x : X)) hh))
    have hQjE : p '' Q.boundary ℝ ⊆ (Subtype.val : End → X) '' range jE := by
      intro x hx
      obtain ⟨y,⟨z,hzy⟩,hyx⟩ := hQj hx
      exact ⟨jE z,mem_range_self z,(congrArg Subtype.val hzy).trans hyx⟩
    have hQB : p '' Q.boundary ℝ ⊆ B := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := hx
      obtain ⟨y,hy,hyp⟩ := hQjE ⟨z,hz,rfl⟩
      have hpEnd : p z ∈ End := hyp ▸ y.property
      rcases hpEnd with hold | hband
      · exact False.elim (hold.1.2.2 (hint ⟨z,hQdepth z hz,rfl⟩))
      · exact hband
    have hT : p '' Ann = E ∩ D :=
      (marked_annular_image_eq_frontier_closure p hp hfront hfull hint hends).trans
        (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
          b.ball.closure_interior).symm
    have hBAnn : B ⊆ p '' Ann := by
      rintro _ ⟨z,hz,rfl⟩
      exact hT.symm.subset (Wc z).property
    exact not_enclosing_polygon_in_punctured_end_disk (by omega) L
      (show B ⊆ End from subset_union_right) F hFi
      (fun x => hFrange.subset (mem_range_self x)) H v hvi hvn hFB
      jE hjiE p hp hpi hBAnn Q hQ hQi hQdepth hQencl hQB hQjE

theorem disjoint_closed_region_of_preconnected_not_subset
    {X : Type*} [TopologicalSpace X] {F T : Set X} {O : Set F}
    (hO : IsOpen O) (hT : IsPreconnected T) (hTF : T ⊆ F)
    (hdis : Disjoint (Subtype.val '' frontier O) T)
    (hnot : ¬ T ⊆ Subtype.val '' closure O) :
    Disjoint (Subtype.val '' closure O) T := by
  let A : Set F := Subtype.val ⁻¹' T
  have hAimage : Subtype.val '' A = T := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩; exact hz
    · intro x hx; exact ⟨⟨x,hTF hx⟩,hx,rfl⟩
  have hA : IsPreconnected A := Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    (hAimage.symm ▸ hT)
  have hAdis : Disjoint (frontier O) A := disjoint_left.mpr (fun x hx ha =>
    disjoint_left.mp hdis (mem_image_of_mem Subtype.val hx) ha)
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hxT
  have hxn : x ∉ frontier O := fun hh =>
    disjoint_left.mp hdis (mem_image_of_mem Subtype.val hh) hxT
  have hxO : x ∈ O := by
    have hh : x ∈ closure O \ frontier O := ⟨hx,hxn⟩
    rwa [closure_sdiff_frontier,hO.interior_eq] at hh
  have hsub := hA.m76_subset_of_disjoint_frontier hO hAdis ⟨x,hxT,hxO⟩
  apply hnot
  intro y hy
  exact ⟨⟨y,hTF hy⟩,subset_closure (hsub hy),rfl⟩

end PoincareConjecture.M76

