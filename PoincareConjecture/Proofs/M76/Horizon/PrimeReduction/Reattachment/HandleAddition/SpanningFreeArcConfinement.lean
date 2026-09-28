import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalAnnularBoundaryLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningAnnularSource
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalClosedEndCover








set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem arc_between_closed_separators_subset_middle
    {X : Type*} [TopologicalSpace X] {I M O C₀ C₁ : Set X}
    (hI : IsClosed I) (hM : IsClosed M) (hO : IsClosed O)
    (hIM : I ∩ M = C₀) (hMO : M ∩ O = C₁) (hIO : Disjoint I O)
    {U q : Set P2} (hU : IsFinitePLBallPair ℝ U q)
    {f : P2 → X} (hf : ContinuousOn f U)
    (hcover : MapsTo f U ((I ∪ M) ∪ O))
    (hfree : Disjoint (f '' (U \ q)) (C₀ ∪ C₁))
    (hmeetI : (f '' U ∩ I).Nonempty) (hmeetO : (f '' U ∩ O).Nonempty) :
    f '' U ⊆ M := by
  have hsep₀ : I ∩ (M ∪ O) = C₀ := by
    rw [inter_union_distrib_left, hIM, disjoint_iff_inter_eq_empty.mp hIO, union_empty]
  have hsep₁ : (I ∪ M) ∩ O = C₁ := by
    rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hIO, empty_union, hMO]
  have hright : f '' U ⊆ M ∪ O := by
    rcases original_arc_image_subset_one_closed_end hI (hM.union hO) hsep₀ hU hf
      (fun x hx => by simpa only [union_assoc] using hcover hx)
      (hfree.mono_right subset_union_left) with h | h
    · obtain ⟨x, hx, hxO⟩ := hmeetO
      exact (disjoint_left.mp hIO (h hx) hxO).elim
    · exact h
  have hleft : f '' U ⊆ I ∪ M := by
    rcases original_arc_image_subset_one_closed_end (hI.union hM) hO hsep₁ hU hf
      hcover (hfree.mono_right subset_union_right) with h | h
    · exact h
    · obtain ⟨x, hx, hxI⟩ := hmeetI
      exact (disjoint_left.mp hIO hxI (h hx)).elim
  intro x hx
  rcases hleft hx with hxI | hxM
  · rcases hright hx with hxM | hxO
    · exact hxM
    · exact (disjoint_left.mp hIO hxI hxO).elim
  · exact hxM


theorem HamiltonMarkedProtectedBall.arc_between_nested_annular_circles
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
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
    {m n : ℕ} (P : Polygon P2 (m+3)) (Q : Polygon P2 (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hPd : ∀ z ∈ P.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (hQd : ∀ z ∈ Q.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    (hnest : closure P.inside ⊆ Q.inside)
    {U q : Set P2} (hU : IsFinitePLBallPair ℝ U q)
    {f : P2 → LatticeHandleAmbient ι κ L} (hf : ContinuousOn f U)
    (hfE : MapsTo f U (frontier (closure (latticeHandleDomain ι κ L \ D))))
    (hfree : Disjoint (f '' (U \ q)) (p '' P.boundary ℝ ∪ p '' Q.boundary ℝ))
    (hmeetP : (f '' U ∩ p '' P.boundary ℝ).Nonempty)
    (hmeetQ : (f '' U ∩ p '' Q.boundary ℝ).Nonempty) :
    f '' U ⊆ p '' (closure Q.inside \ P.inside) ∧
      f '' U ⊆ interior (latticeHandleDomain ι κ L) := by
  classical
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  let I := Ann ∩ closure P.inside
  let M := closure Q.inside \ P.inside
  let O := Ann \ Q.inside
  obtain ⟨hIc,hMc,hOc,hcov,hIM,hMO,hIO,hId,hMd,hOd⟩ :=
    nested_enclosing_annular_source_partition P Q hP hPi hQ hQi hPd hQd hencl hnest
  change IsCompact I at hIc
  change IsCompact M at hMc
  change IsCompact O at hOc
  have hIA : I ⊆ Ann := inter_subset_left
  have hOA : O ⊆ Ann := sdiff_subset
  have hMA : M ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hMd z hz).1.le,(hMd z hz).2.le⟩
  have hT : p '' Ann = E ∩ D :=
    (marked_annular_image_eq_frontier_closure p hp hfront hfull hint hends).trans
      (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
        b.ball.closure_interior).symm
  have hcover : (E ∩ frontier R) ∪ (p '' Ann) = frontier E := by
    obtain ⟨_,_,_,hcontact,_,_,hfr⟩ := b.closed_complement_geometry he hdim hi
    rw [hT,hfr,←hcontact]
    exact union_comm _ _
  obtain ⟨a,ha,hl⟩ := b.exists_original_annular_boundary_labels he hdim hi p hp hpi
    hfront hfull hint hends
  let A : Bool → Set X := fun side => {x | x ∈ E ∩ frontier R ∧ x.1 = a side}
  have hAc : ∀ side, IsClosed (A side) := fun side =>
    (isClosed_closure.inter isClosed_frontier).inter
      (isClosed_eq continuous_fst continuous_const)
  have hAdis : Disjoint (A true) (A false) := by
    apply disjoint_left.mpr
    intro x ht hf
    have hh : a true = a false := Subtype.ext (ht.2.symm.trans hf.2)
    exact Bool.noConfusion (ha.1 hh)
  have hAcov : A true ∪ A false = E ∩ frontier R := by
    apply Subset.antisymm (union_subset (fun _ h => h.1) (fun _ h => h.1))
    intro x hx
    have hx1 : x.1 ∈ sphere (0 : ι → ℝ) 1 := by
      have hh := hx.2
      change x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ univ) at hh
      rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hh
      exact hh.1
    obtain ⟨side,hs⟩ := ha.2 ⟨x.1,hx1⟩
    have hs' : x.1 = a side := (congrArg Subtype.val hs).symm
    cases side
    · exact Or.inr ⟨hx,hs'⟩
    · exact Or.inl ⟨hx,hs'⟩
  have hend : ∀ side z, z ∈ Ann → p z ∈ A side →
      depth 8 z = (if side then 1 else -1) := by
    intro side z hz hx
    rcases (hends ⟨z,hz⟩).mp hx.1.2 with hm | hpz
    · have hh : a false = a side := Subtype.ext ((hl false ⟨z,hz⟩ hm).symm.trans hx.2)
      have hs := ha.1 hh
      subst side
      exact hm
    · have hh : a true = a side := Subtype.ext ((hl true ⟨z,hz⟩ hpz).symm.trans hx.2)
      have hs := ha.1 hh
      subst side
      exact hpz
  have hMI : Disjoint (p '' M) (A true ∪ A false) := by
    apply disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ (hx | hx)
    · have hh := hend true z (hMA hz) hx
      exact (ne_of_lt (hMd z hz).2) hh
    · have hh := hend false z (hMA hz) hx
      exact (ne_of_gt (hMd z hz).1) hh
  have hIF : Disjoint (p '' I) (A false) := by
    apply disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hx
    exact (ne_of_gt (hId z hz)) (hend false z (hIA hz) hx)
  have hOT : Disjoint (p '' O) (A true) := by
    apply disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hx
    exact (ne_of_lt (hOd z hz)) (hend true z (hOA hz) hx)
  have himageinter : ∀ {s t : Set P2}, s ⊆ Ann → t ⊆ Ann →
      p '' s ∩ p '' t = p '' (s ∩ t) := by
    intro s t hs ht
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,w,hw,hwz⟩
      have hh := hpi (ht hw) (hs hz) hwz
      exact ⟨z,⟨hz,hh ▸ hw⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz.1,rfl⟩,z,hz.2,rfl⟩
  have hleft : (A true ∪ p '' I) ∩ (p '' M) = p '' P.boundary ℝ := by
    rw [union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp (hMI.mono_right subset_union_left).symm,
      empty_union,himageinter hIA hMA,hIM]
  have hright : (p '' M) ∩ (A false ∪ p '' O) = p '' Q.boundary ℝ := by
    rw [inter_union_distrib_left,
      disjoint_iff_inter_eq_empty.mp (hMI.mono_right subset_union_right),
      empty_union,himageinter hMA hOA,hMO]
  have hdis : Disjoint (A true ∪ p '' I) (A false ∪ p '' O) := by
    refine disjoint_left.mpr ?_
    rintro x (hx | hx) (hy | hy)
    · exact disjoint_left.mp hAdis hx hy
    · exact disjoint_left.mp hOT hy hx
    · exact disjoint_left.mp hIF hx hy
    · have hh : x ∈ p '' (I ∩ O) := (himageinter hIA hOA).subset ⟨hx,hy⟩
      rcases hh with ⟨z,hz,_⟩
      exact disjoint_left.mp hIO hz.1 hz.2
  have hcov' : ((A true ∪ p '' I) ∪ p '' M) ∪ (A false ∪ p '' O) = frontier E := by
    calc
      _ = (A true ∪ A false) ∪ p '' ((I ∪ M) ∪ O) := by
        simp only [image_union]
        ext x
        simp only [mem_union]
        tauto
      _ = frontier E := by rw [hcov,hAcov,hcover]
  have hsub : f '' U ⊆ p '' M := arc_between_closed_separators_subset_middle
    ((hAc true).union (hIc.image_of_continuousOn (hp.mono hIA)).isClosed)
    (hMc.image_of_continuousOn (hp.mono hMA)).isClosed
    ((hAc false).union (hOc.image_of_continuousOn (hp.mono hOA)).isClosed)
    hleft hright hdis hU hf (fun z hz => hcov'.symm.subset (hfE hz)) hfree
    (by obtain ⟨x,hx,hxp⟩ := hmeetP
        exact ⟨x,hx,(hleft.symm.subset hxp).1⟩)
    (by obtain ⟨x,hx,hxq⟩ := hmeetQ
        exact ⟨x,hx,(hright.symm.subset hxq).2⟩)
  exact ⟨hsub,fun x hx => by
    obtain ⟨z,hz,rfl⟩ := hsub hx
    exact hint ⟨z,hMd z hz,rfl⟩⟩

theorem HamiltonMarkedProtectedBall.original_spanning_free_arc_subset_lateral
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
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
    {m n : ℕ} (P : Polygon P2 (m+3)) (Q : Polygon P2 (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hPd : ∀ z ∈ P.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (hQd : ∀ z ∈ Q.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (henclP : Dehn.annulusSquare 8 1 ⊆ P.inside)
    (henclQ : Dehn.annulusSquare 8 1 ⊆ Q.inside)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    {S : Set (LatticeHandleAmbient ι κ L)} {A U C : Set P2}
    {f : P2 → LatticeHandleAmbient ι κ L}
    (hcontact : p '' P.boundary ℝ ∪ p '' Q.boundary ℝ ⊆ S)
    (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U (U ∩ C))
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hS : f '' A ∩ S = f '' C)
    (hfE : f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U)
    (hmeetP : (f '' U ∩ p '' P.boundary ℝ).Nonempty)
    (hmeetQ : (f '' U ∩ p '' Q.boundary ℝ).Nonempty) :
    f '' U ⊆ interior (latticeHandleDomain ι κ L) ∧
      f '' U ⊆ closure (latticeHandleDomain ι κ L \ D) ∩ D := by
  have hUA : U ⊆ A := fun x hx => hA.1 (Or.inl hx)
  have hCA : C ⊆ A := fun x hx => hA.1 (Or.inr hx)
  have hfU : MapsTo f U (frontier (closure (latticeHandleDomain ι κ L \ D))) :=
    fun x hx => (hfE.symm.subset ⟨x,hx,rfl⟩).2
  have hfree : Disjoint (f '' (U \ (U ∩ C)))
      (p '' P.boundary ℝ ∪ p '' Q.boundary ℝ) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    obtain ⟨w,hw,hwz⟩ := hS.subset ⟨⟨z,hUA hz.1,rfl⟩,hcontact hx⟩
    have heq := hfi (hCA hw) (hUA hz.1) hwz
    exact hz.2 ⟨hz.1,heq ▸ hw⟩
  have hT : p '' Ann = closure (latticeHandleDomain ι κ L \ D) ∩ D :=
    (marked_annular_image_eq_frontier_closure p hp hfront hfull hint hends).trans
      (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
        b.ball.closure_interior).symm
  have hfinish : ∀ {s : Set P2}, s ⊆ Ann → f '' U ⊆ p '' s →
      f '' U ⊆ interior (latticeHandleDomain ι κ L) →
      f '' U ⊆ interior (latticeHandleDomain ι κ L) ∧
        f '' U ⊆ closure (latticeHandleDomain ι κ L \ D) ∩ D := by
    intro s hs hfs hfr
    exact ⟨hfr,fun x hx => hT.subset ((image_mono hs) (hfs hx))⟩
  rcases Dehn.Annuli.enclosing_source_polygons_nested P Q hP hPi hQ hQi hdis
    (show 2 * (1 : ℝ) < 8 by norm_num) henclP henclQ with hnest | hnest
  · obtain ⟨hs,hr⟩ := b.arc_between_nested_annular_circles he hdim hi p hp hpi
      hfront hfull hint hends P Q hP hPi hQ hQi hPd hQd henclP hnest
      hU (hf.mono hUA) hfU hfree hmeetP hmeetQ
    obtain ⟨_,_,_,hcover,_,_,_,_,_,_⟩ :=
      nested_enclosing_annular_source_partition P Q hP hPi hQ hQi hPd hQd henclP hnest
    exact hfinish (fun z hz => hcover.subset (Or.inl (Or.inr hz))) hs hr
  · obtain ⟨hs,hr⟩ := b.arc_between_nested_annular_circles he hdim hi p hp hpi
      hfront hfull hint hends Q P hQ hQi hP hPi hQd hPd henclQ hnest
      hU (hf.mono hUA) hfU (by simpa only [union_comm] using hfree) hmeetQ hmeetP
    obtain ⟨_,_,_,hcover,_,_,_,_,_,_⟩ :=
      nested_enclosing_annular_source_partition Q P hQ hQi hP hPi hQd hPd henclQ hnest
    exact hfinish (fun z hz => hcover.subset (Or.inl (Or.inr hz))) hs hr

end PoincareConjecture.M76
