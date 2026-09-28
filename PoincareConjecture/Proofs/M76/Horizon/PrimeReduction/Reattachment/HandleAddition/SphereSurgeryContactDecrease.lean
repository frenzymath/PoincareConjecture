import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereSurgeryNonbounding
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreComponentCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SeparatedSubcomplex










set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_separated_sphere_contact_positions
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S F U : Set X}
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (N : Bool → Set X) (spheres : ∀ i, ChartwisePLSphere e (N i))
    (hU : IsClosed U) (hUF : Disjoint U F)
    (hdis : Disjoint (N false) (N true))
    (houtside : (N false ∪ N true) \ U = S \ U)
    (hCQ : S ∩ F ⊆ Q.source)
    (hG : G.faces.Finite) (hGs : G.space = Q '' (S ∩ F))
    (hpres : HasDisjointPolygonPresentation G.space)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0)
    (hne : ∀ i, (N i ∩ F).Nonempty) :
    ∃ H : Bool → SimplicialComplex ℝ V3, ∀ i,
      H i ≤ G ∧ (H i).faces.Finite ∧
      (H i).space = Q '' (N i ∩ F) ∧ N i ∩ F ⊆ Q.source ∧
      HasDisjointPolygonPresentation (H i).space ∧
      (∀ a ∈ (H i).faces, a.card ≤ 2) ∧
      (∀ v : (H i).vertices,
        ((H i).vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      Nat.card (ConnectedComponents (H i).space) < Nat.card (ConnectedComponents G.space) ∧
      ∀ w ∈ (H i).space, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
          (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧
          LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, Q.symm x ∈ N i ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0 := by
  classical
  have hdis' (i : Bool) : Disjoint (N i) (N (!i)) := by
    cases i
    · exact hdis
    · exact hdis.symm
  have hnotU {x : X} (hx : x ∈ F) : x ∉ U := fun h => disjoint_left.mp hUF h hx
  have hcov : (N false ∩ F) ∪ (N true ∩ F) = S ∩ F := by
    ext x
    constructor
    · rintro (⟨hx,hf⟩ | ⟨hx,hf⟩)
      · exact ⟨(houtside.subset ⟨Or.inl hx,hnotU hf⟩).1,hf⟩
      · exact ⟨(houtside.subset ⟨Or.inr hx,hnotU hf⟩).1,hf⟩
    · rintro ⟨hx,hf⟩
      rcases (houtside.symm.subset ⟨hx,hnotU hf⟩).1 with h | h
      · exact Or.inl ⟨h,hf⟩
      · exact Or.inr ⟨h,hf⟩
  have hsub (i : Bool) : N i ∩ F ⊆ S ∩ F := by
    cases i
    · exact subset_union_left.trans hcov.subset
    · exact subset_union_right.trans hcov.subset
  have hNQ (i : Bool) : N i ∩ F ⊆ Q.source := (hsub i).trans hCQ
  have hGT : G.space ⊆ Q.target := by
    rw [hGs]
    rintro _ ⟨x,hx,rfl⟩
    exact Q.map_source (hCQ hx)
  have hphys : Q.symm '' G.space = S ∩ F := by
    rw [hGs]
    ext x
    constructor
    · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
      simpa only [Q.left_inv (hCQ hy)] using hy
    · intro hx
      exact ⟨Q x,⟨x,hx,rfl⟩,Q.left_inv (hCQ hx)⟩
  have hcover (i : Bool) : Q.symm '' G.space ⊆ N i ∪ N (!i) := by
    rw [hphys,←hcov]
    cases i <;> rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr hx.1
    · exact Or.inr hx.1
    · exact Or.inl hx.1
  choose H hHG hH hHs hHphys hHdegree using fun i =>
    G.exists_subcomplex_of_closed_image_partition hG Q.symm
      (Q.symm.continuousOn.mono hGT) (spheres i).isCompact.isClosed
      (spheres (!i)).isCompact.isClosed (hdis' i) (hcover i)
  have hHs' (i : Bool) : (H i).space = Q '' (N i ∩ F) := by
    rw [hHs i]
    ext z
    constructor
    · rintro ⟨hz,hzi⟩
      obtain ⟨x,hx,hxz⟩ := hGs.subset hz
      subst z
      simp only [mem_preimage,Q.left_inv (hCQ hx)] at hzi
      exact ⟨x,⟨hzi,hx.2⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hGs.symm.subset ⟨x,hsub i hx,rfl⟩,by
        simpa only [mem_preimage,Q.left_inv (hNQ i hx)] using hx.1⟩
  have hHC (i : Bool) : IsCompact (H i).space := (H i).isCompact_space_of_finite (hH i)
  have hHdis : Disjoint (H false).space (H true).space := by
    rw [hHs false,hHs true]
    exact disjoint_left.mpr (fun z hz hz' => disjoint_left.mp hdis hz.2 hz'.2)
  have hHcover : (H false).space ∪ (H true).space = G.space := by
    rw [hHs' false,hHs' true,← image_union,hcov,hGs]
  have hHp := (hHcover.symm ▸ hpres).closed_cut (hHC false).isClosed (hHC true).isClosed hHdis
  have hHP (i : Bool) : HasDisjointPolygonPresentation (H i).space := by
    cases i
    · exact hHp.1
    · exact hHp.2
  have hpos (i : Bool) : 0 < Nat.card (ConnectedComponents (H i).space) := by
    have hn' : (H i).space.Nonempty := by
      rw [hHs' i]
      exact (hne i).image Q
    have hh := cocore_component_count_eq_zero_iff (hHP i)
    have hz : Nat.card (ConnectedComponents (H i).space) ≠ 0 :=
      fun h => hn'.ne_empty (hh.mp h)
    omega
  have hcount := cocore_component_count_closed_partition hpres
    (hHC false).isClosed (hHC true).isClosed hHdis hHcover
  refine ⟨H,fun i => ⟨hHG i,hH i,hHs' i,hNQ i,hHP i,
    fun a ha => hGc a (hHG i ha),fun v => (hHdegree i v).trans (hdegree _),?_,?_⟩⟩
  · cases i <;> have := hpos false <;> have := hpos true <;> omega
  · intro w hw O hO hwO
    have hwG := SimplicialComplex.space_subset_of_le (hHG i) hw
    have hwi : Q.symm w ∈ N i := by
      rw [hHs i] at hw
      exact hw.2
    have hwF : Q.symm w ∈ F := (hphys.subset ⟨w,hwG,rfl⟩).2
    let V := (U ∪ N (!i))ᶜ
    have hV : IsOpen V := (hU.union (spheres (!i)).isCompact.isClosed).isOpen_compl
    have hwV : Q.symm w ∈ V := by
      rintro (hu | hn)
      · exact hnotU hwF hu
      · exact disjoint_left.mp (hdis' i) hwi hn
    obtain ⟨C,hwC,hCO,hCR,hC0,hC,hCi,hCS,hCF⟩ := hcross w hwG
      (O ∩ (Q.target ∩ Q.symm ⁻¹' V)) (hO.inter (Q.symm.isOpen_inter_preimage hV))
      ⟨hwO,hGT hwG,hwV⟩
    refine ⟨C,hwC,fun z hz => ⟨(hCO hz).1.1,(hCO hz).2⟩,hCR,hC0,hC,hCi,?_,hCF⟩
    intro z hz
    have hzV := (hCO hz).1.2.2
    have hzU : Q.symm z ∉ U := fun h => hzV (Or.inl h)
    have hzN : Q.symm z ∉ N (!i) := fun h => hzV (Or.inr h)
    have hm : Q.symm z ∈ N i ↔ Q.symm z ∈ S := by
      have hh : Q.symm z ∈ N false ∪ N true ↔ Q.symm z ∈ S := by
        constructor
        · intro hn
          exact (houtside.subset ⟨hn,hzU⟩).1
        · intro hs
          exact (houtside.symm.subset ⟨hs,hzU⟩).1
      cases i <;> simp only [Bool.not_false,Bool.not_true] at hzN ⊢ <;>
        simp only [mem_union] at hh <;> tauto
    exact hm.trans (hCS z hz)

theorem OriginalDiskProduct.exists_smaller_nonbounding_contact_position
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R W S F : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e W j) (he : PLDomain e R) (hR : IsCompact R)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (hUR : P.closedStrip ⊆ interior R) (hUF : Disjoint P.closedStrip F)
    (ret : Bool → Set X) (hretS : ∀ i, ret i ⊆ S)
    (hretstrip : ∀ i, ret i ∩ P.closedStrip = P.capRimSet i)
    (hretout : ∀ i, (ret i \ P.capDisk i).Nonempty)
    (hcover : (ret false ∪ ret true) ∪
      P.map '' (sphere (0 : Fin 2 → ℝ) 1 ×ˢ Icc (-(1/2 : ℝ)) (1/2)) = S)
    (spheres : ∀ i, ChartwisePLSphere e (ret i ∪ P.capDisk i))
    (hdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true))
    (houtside : ((ret false ∪ P.capDisk false) ∪ (ret true ∪ P.capDisk true)) \
      P.closedStrip = S \ P.closedStrip)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hCQ : S ∩ F ⊆ Q.source)
    (hG : G.faces.Finite) (hGs : G.space = Q '' (S ∩ F))
    (hpres : HasDisjointPolygonPresentation G.space)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0)
    (hne : ∀ i, ((ret i ∪ P.capDisk i) ∩ F).Nonempty) :
    ∃ (i : Bool) (H : SimplicialComplex ℝ V3),
      let N := ret i ∪ P.capDisk i
      Nonempty (ChartwisePLSphere e N) ∧ N ⊆ interior R ∧
      (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B N)) ∧
      N ∩ F ⊆ Q.source ∧ H.faces.Finite ∧ H.space = Q '' (N ∩ F) ∧
      HasDisjointPolygonPresentation H.space ∧
      (∀ a ∈ H.faces, a.card ≤ 2) ∧
      (∀ v : H.vertices, (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      Nat.card (ConnectedComponents H.space) < Nat.card (ConnectedComponents G.space) ∧
      ∀ w ∈ H.space, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
          (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧
          LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, Q.symm x ∈ N ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0 := by
  classical
  have hbranch : ∃ i, ¬ ∃ B, B ⊆ R ∧
      Nonempty (ChartwisePLBall e B (ret i ∪ P.capDisk i)) := by
    by_contra h
    push Not at h
    exact hn (P.sphere_bounds_of_two_separated_cap_fillings he hR s hSR hUR
      ret hretS hretstrip hretout hcover spheres hdis h)
  obtain ⟨H,hH⟩ := exists_separated_sphere_contact_positions Q G
    (fun i => ret i ∪ P.capDisk i) spheres
    (P.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed
    hUF hdis houtside hCQ hG hGs hpres hGc hdegree hcross hne
  obtain ⟨i,hni⟩ := hbranch
  obtain ⟨_,hHi,hHs,hNQ,hHp,hHc,hHd,hlt,hHC⟩ := hH i
  have hcapU : P.capDisk i ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases i
    · exact subset_union_left
    · exact subset_union_right
  exact ⟨i,H i,⟨spheres i⟩,union_subset ((hretS i).trans hSR) (hcapU.trans hUR),
    hni,hNQ,hHi,hHs,hHp,hHc,hHd,hlt,hHC⟩

theorem OriginalDiskProduct.not_both_contacts_of_minimal_position
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R W S F D : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e W j) (he : PLDomain e R) (hR : IsCompact R)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (hUR : P.closedStrip ⊆ interior R) (hUF : Disjoint P.closedStrip F)
    (ret : Bool → Set X) (hretS : ∀ i, ret i ⊆ S)
    (hretstrip : ∀ i, ret i ∩ P.closedStrip = P.capRimSet i)
    (hretout : ∀ i, (ret i \ P.capDisk i).Nonempty)
    (hcover : (ret false ∪ ret true) ∪
      P.map '' (sphere (0 : Fin 2 → ℝ) 1 ×ˢ Icc (-(1/2 : ℝ)) (1/2)) = S)
    (spheres : ∀ i, ChartwisePLSphere e (ret i ∪ P.capDisk i))
    (hdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true))
    (houtside : ((ret false ∪ P.capDisk false) ∪ (ret true ∪ P.capDisk true)) \
      P.closedStrip = S \ P.closedStrip)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hCQ : S ∩ F ⊆ Q.source)
    (hG : G.faces.Finite) (hGs : G.space = Q '' (S ∩ F))
    (hpres : HasDisjointPolygonPresentation G.space)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ F ↔ (C x).1.1 = 0)
    (hDQ : D ⊆ Q.source)
    (hQ : ∀ a, (e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hmin : ∀ d : Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3,
      (Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ a, (e a).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
        d.1 ∩ F ⊆ d.2.1.source ∧
        d.2.2.faces.Finite ∧ d.2.2.space = d.2.1 '' (d.1 ∩ F) ∧
        HasDisjointPolygonPresentation d.2.2.space ∧
        (∀ a ∈ d.2.2.faces, a.card ≤ 2) ∧
        (∀ v : d.2.2.vertices,
          (d.2.2.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        ∀ w ∈ d.2.2.space, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧
            (∀ z ∈ C.source, d.2.1.symm z ∈ interior R) ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧
            LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
            ∀ x ∈ C.source, d.2.1.symm x ∈ F ↔ (C x).1.1 = 0) →
      Nat.card (ConnectedComponents G.space) ≤
        Nat.card (ConnectedComponents d.2.2.space)) :
    ¬ ∀ i, ((ret i ∪ P.capDisk i) ∩ F).Nonempty := by
  intro hne
  obtain ⟨i,H,hs,hNR,hnN,hNQ,hH,hHs,hHp,hHc,hHd,hlt,hHC⟩ :=
    P.exists_smaller_nonbounding_contact_position he hR s hSR hn hUR hUF
      ret hretS hretstrip hretout hcover spheres hdis houtside
      Q G hCQ hG hGs hpres hGc hdegree hcross hne
  exact (Nat.not_le_of_gt hlt) (hmin (ret i ∪ P.capDisk i,Q,H)
    ⟨hs,hNR,hnN,hDQ,hQ,hNQ,hH,hHs,hHp,hHc,hHd,hHC⟩)

end PoincareConjecture.M76
