import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PrescribedProductCircleGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedSeparatedCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SeparatedCircleSphereAssembly
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryContactLedger
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ProtectedCircleNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCofaceTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.CircleSurgeryGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SelectedCircleSurgeryGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SelectedCircleContactCounts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SelectedCircleGraphPosition

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

open scoped Classical in
theorem OriginalDiskProduct.exists_selected_positioned_circle_graph
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R Z O : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i)) (i : κ)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K : SimplicialComplex ℝ E) (g : E → X) {s : Finset E} (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (G : SimplicialComplex ℝ V3) (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysical : Q.symm '' G.space = (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)))
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hSZ : Disjoint (⋃ i, S i) Z) (hOZ : Disjoint O Z)
    (hOfaces : ∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
      Disjoint O (g '' convexHull ℝ (a : Set E)))
    (hOmembers : ∀ a, a ≠ i → Disjoint O (S a))
    (hpO : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) O)
    (hproper : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S i ↔ z.1 ∈ Rim)
    (ret : Bool → Set X) (hretDis : Disjoint (ret true) (ret false))
    (hretContact : ∀ b, ret b ∩ P.closedStrip = P.capRimSet b)
    (hcover : (ret true ∪ ret false) ∪ P.map '' (Rim ×ˢ J) = S i)
    (t : ∀ b, ChartwisePLSphere e (ret b ∪ P.capDisk b))
    (hcapF : ∀ b, Disjoint (P.capDisk b) (g '' convexHull ℝ (s : Set E)))
    (hbandF : (P.map '' (Rim ×ˢ J)) ∩ (g '' convexHull ℝ (s : Set E)) =
      Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (b : Bool) :
    let new := fun a => ret a ∪ P.capDisk a
    let S' := selectedCircleSurgeryFamily S i new b
    ∃ (H : SimplicialComplex ℝ V3) (_hHG : H ≤ G.deleteEdgeComponent C),
      Nonempty (∀ a, ChartwisePLSphere e (S' a)) ∧
      (Pairwise fun a c => Disjoint (S' a) (S' c)) ∧ Disjoint (⋃ a, S' a) Z ∧
      (∀ a v, v ∈ K.faces → v.card = 2 → HasOriginalEdgeCofaceCharts e (S' a) K g v) ∧
      (⋃ a, S' a) \ O ⊆ (⋃ a, S a) \ O ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (⋃ v, S' v) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ v, S v) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (⋃ a, S' a) ∩ (g '' convexHull ℝ (s : Set E)) ⊆
        ((⋃ a, S a) ∩ (g '' convexHull ℝ (s : Set E))) \
          (Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))) ∧
      H.faces.Finite ∧ H.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ a ∈ H.faces, a.card ≤ 2) ∧
      Q.symm '' H.space = (⋃ a, S' a) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ v : H.vertices, (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : H.vertices, (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (H.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      H.faces.ncard < G.faces.ncard ∧
      (∀ w ∈ H.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ V : Set V3, IsOpen V → w ∈ V →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ ⋃ a, S' a ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      ∀ a ∈ K.faces, a.card = 3 → a ≠ s →
        ∀ (Q' : OpenPartialHomeomorph X V3) (A' : E →ᴬ[ℝ] V3),
          (InNonreturningTriangleGraphPosition Q' (⋃ j, S j) g a A' →
            InNonreturningTriangleGraphPosition Q' (⋃ j, S' j) g a A') ∧
          (InCircleFreeNonreturningTriangleGraphPosition Q' (⋃ j, S j) g a A' →
            InCircleFreeNonreturningTriangleGraphPosition Q' (⋃ j, S' j) g a A') := by
  classical
  let new := fun a => ret a ∪ P.capDisk a
  obtain ⟨hnewDis,hSupport,hFace,hStripFace,hStripCompact⟩ :=
    P.positioned_circle_contact_geometry ret hretDis hretContact hcover hproper hcapF hbandF
  have hStripO : P.closedStrip ⊆ O := by
    rintro x ⟨z,hz,rfl⟩
    exact hpO ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hretS (a : Bool) : ret a ⊆ S i := by
    intro x hx
    apply hcover.subset
    cases a
    · exact Or.inl (Or.inr hx)
    · exact Or.inl (Or.inl hx)
  have hcapO (a : Bool) : P.capDisk a ⊆ O := by
    rintro x ⟨z,hz,rfl⟩
    exact hpO (OriginalDiskProduct.cap_source_subset a hz)
  have hnewOther (a : Bool) (v : κ) (hv : v ≠ i) : Disjoint (new a) (S v) :=
    disjoint_union_left.mpr ⟨(hdis hv.symm).mono_left (hretS a),
      (hOmembers v hv).mono_left (hcapO a)⟩
  have hnewZ (a : Bool) : Disjoint (new a) Z :=
    disjoint_union_left.mpr ⟨hSZ.mono_left ((hretS a).trans (subset_iUnion S i)),
      hOZ.mono_left (hcapO a)⟩
  obtain ⟨sfull⟩ := circleSurgeryFamily_spheres S i new sS t
  have hfull := circleSurgeryFamily_pairwise_disjoint S i new hdis hnewDis hnewOther
  have hfullZ := circleSurgeryFamily_disjoint_marked S i new hSZ hnewZ
  have hCO : Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ O :=
    hStripFace.symm.subset.trans (inter_subset_left.trans hStripO)
  obtain ⟨hG',hGT',hdim',hphysical',hinterior',hexterior',hfinite',_,_⟩ :=
    circleSurgeryFamily_graph S i new Q G C hG hGT hphysical hdim hinterior hexterior
      hfinite hCO hOmembers hFace
  have hFamilySupport := circleSurgeryFamily_sdiff S i new hSupport
  have hFamilyFace := circleSurgeryFamily_inter S i new hCO hOmembers hFace
  have hSupportGraph : P.closedStrip ∩ ((⋃ a, S a) ∩ (g '' convexHull ℝ (s : Set E))) =
      Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) := by
    rw [← hStripFace]
    ext x
    constructor
    · rintro ⟨hx,hfam,hF⟩
      obtain ⟨a,ha⟩ := mem_iUnion.mp hfam
      have hai : a = i := by
        by_contra hai
        exact disjoint_left.mp (hOmembers a hai) (hStripO hx) ha
      exact ⟨hx,hai ▸ ha,hF⟩
    · exact fun hx => ⟨hx.1,(subset_iUnion S i) hx.2.1,hx.2.2⟩
  have hOther (a : Finset E) (ha : a ∈ K.faces) (hac : a.card ≤ 3) (hane : a ≠ s) :
      (new true ∪ new false) ∩ (g '' convexHull ℝ (a : Set E)) =
        S i ∩ (g '' convexHull ℝ (a : Set E)) := by
    ext x
    have hout (hx : x ∈ g '' convexHull ℝ (a : Set E)) : x ∉ P.closedStrip :=
      fun hc => disjoint_left.mp (hOfaces a ha hac hane) (hStripO hc) hx
    exact ⟨fun hx => ⟨(hSupport.subset ⟨hx.1,hout hx.2⟩).1,hx.2⟩,
      fun hx => ⟨(hSupport.symm.subset ⟨hx.1,hout hx.2⟩).1,hx.2⟩⟩
  have hfullCofaces : ∀ a v, v ∈ K.faces → v.card = 2 →
      HasOriginalEdgeCofaceCharts e (circleSurgeryFamily S i new a) K g v := by
    intro a v hv hv2
    cases a with
    | inl a => exact hcofaces a.val v hv hv2
    | inr a =>
      have hvne : v ≠ s := by intro hh; have := congrArg Finset.card hh; omega
      have hpair := (hcofaces i v hv hv2).surgery_pair_of_disjoint_support hStripCompact.isClosed
        (t true).isCompact (t false).isCompact hnewDis
        ((hOfaces v hv (by omega) hvne).mono_left hStripO) hSupport
      cases a
      · exact hpair.2
      · exact hpair.1
  have hcrossings' : ∀ w ∈ (G.deleteEdgeComponent C).space ∩
      intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ a, circleSurgeryFamily S i new a ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
    intro w hw
    have hwQ := (hGT' hw.1).2
    have hwOld := hFamilyFace.subset (hphysical'.subset ⟨w,hw.1,rfl⟩)
    have hwC : Q.symm w ∉ P.closedStrip := fun hc =>
      hwOld.2 (hSupportGraph.subset ⟨hc,hwOld.1⟩)
    have hwG : w ∈ G.space := by
      obtain ⟨z,hz,hzw⟩ := hphysical.symm.subset hwOld.1
      exact (Q.symm.injOn (hGT hz).2 hwQ hzw) ▸ hz
    exact paired_face_crossings_of_equal_off_closed Q hStripCompact.isClosed
      hFamilySupport hwQ hwC (hcrossings w ⟨hwG,hw.2⟩)
  obtain ⟨hsselected,hselectedDis,hselectedZ,hselectedSub,_⟩ :=
    selectedCircleSurgeryFamily_geometry S i new b sfull hfull hfullZ
  obtain ⟨H,hHG,hH,hspace,himage,_,hdegree⟩ :=
    exists_selected_circle_surgery_graph S i new b sfull hfull Q
      (G.deleteEdgeComponent C) hG' (hGT'.trans inter_subset_right) hphysical'
  have hsub : H.space ⊆ (G.deleteEdgeComponent C).space := hspace ▸ inter_subset_left
  refine ⟨H,hHG,hsselected,hselectedDis,hselectedZ,?_,?_,?_,?_,hH,hsub.trans hGT',
    (fun a ha => hdim' a (hHG ha)),himage,?_,?_,
    hfinite'.subset (inter_subset_inter_left _ hsub),
    (G.faces_ncard_lt_of_le_deleteEdgeComponent hG C H hHG).2,?_,?_⟩
  · intro a v hv hv2
    rw [selectedCircleSurgeryFamily_eq_index]
    exact hfullCofaces _ v hv hv2
  · intro x hx
    have hout : x ∉ P.closedStrip := fun hc => hx.2 (hStripO hc)
    exact ⟨(hFamilySupport.subset ⟨hselectedSub hx.1,hout⟩).1,hx.2⟩
  · intro a ha hac hane
    exact selectedCircleSurgeryFamily_inter_subset_of_full S i new b
      (circleSurgeryFamily_inter_eq S i new (hOther a ha hac hane)).subset
  · exact (inter_subset_inter_left _ hselectedSub).trans hFamilyFace.subset
  · intro v hv
    exact (hdegree v).trans (hinterior' ⟨v.val,hHG v.property⟩ hv)
  · intro v hv
    exact (hdegree v).trans (hexterior' ⟨v.val,hHG v.property⟩ hv)
  · intro w hw
    have hh := hw.1
    rw [hspace] at hh
    exact selected_circle_surgery_paired_crossings S i new b sfull hfull Q
      (hGT' hh.1).2 hh.2 (hcrossings' w ⟨hh.1,hw.2⟩)
  · intro a ha ha3 hane Q' A'
    have hmiss := (hOfaces a ha ha3.le hane).mono_left hStripO
    constructor
    · intro hpos
      exact (hpos.of_equal_off_closed hStripCompact.isClosed hmiss hFamilySupport).selected_circle_surgery
        S i new b sfull hfull
    · intro hpos
      exact (hpos.of_equal_off_closed hStripCompact.isClosed hmiss hFamilySupport).selected_circle_surgery
        S i new b sfull hfull

end PoincareConjecture.M76
