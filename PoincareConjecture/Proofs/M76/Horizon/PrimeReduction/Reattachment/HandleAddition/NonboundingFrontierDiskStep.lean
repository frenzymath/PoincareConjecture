import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PrescribedNonboundingSurgery
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FrontierCircleSurgeryRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.IsolatedContactCircle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.SphereFrontierFamilyDecrease
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreGerm
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FrontierCrossingTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PrescribedProductCircleGeometry

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem ChartwisePLSphere.exists_nonbounding_frontier_disk_step
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S T : Set X}
    (s : ChartwisePLSphere e S) (t : ChartwisePLSphere e T)
    (hR : IsCompact R) (he : PLDomain e R) (hSR : S ⊆ interior R) (hTR : T ⊆ R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) (hTQ : T ⊆ Q.source)
    (hpres : HasDisjointPolygonPresentation (Q '' (S ∩ T)))
    (hcross : ∀ w ∈ Q '' (S ∩ T), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧ LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ T ↔ (C x).1.1 = 0)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hpR : p '' d ⊆ interior R)
    (hcontact : p '' d ∩ S = p '' r)
    (hrem : IsCompact ((S ∩ T) \ p '' r))
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d) :
    ∃ (N : Set X) (_sN : ChartwisePLSphere e N),
      N ⊆ interior R ∧
      (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B N)) ∧
      HasDisjointPolygonPresentation (Q '' (N ∩ T)) ∧
      N ∩ T ⊆ S ∩ T ∧
      Nat.card (ConnectedComponents ↥(Q '' (N ∩ T))) <
        Nat.card (ConnectedComponents ↥(Q '' (S ∩ T))) ∧
      ∃ V : Set X, IsOpen V ∧ N ∩ T ⊆ V ∧
        (∀ x ∈ V, x ∈ N ↔ x ∈ S) ∧
        ∀ w ∈ Q '' (N ∩ T), ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧ LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ x ∈ C.source, Q.symm x ∈ N ↔ (C x).2 = 0) ∧
            ∀ x ∈ C.source, Q.symm x ∈ T ↔ (C x).1.1 = 0 := by
  classical
  have hprST : p '' r ⊆ S ∩ T := by
    intro x hx
    exact ⟨(hcontact.symm.subset hx).2,hpT ((image_mono hd.1) hx)⟩
  have hrOpen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r)) := by
    have heq : (Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r) =
        (Subtype.val ⁻¹' ((S ∩ T) \ p '' r))ᶜ := by
      ext x
      simp only [mem_preimage,mem_compl_iff,mem_sdiff,x.property,true_and,not_not]
    rw [heq]
    exact (hrem.isClosed.preimage continuous_subtype_val).isOpen_compl
  obtain ⟨rho,hρ,hρi,hρR,hρS,hρcaps,hρband⟩ :=
    t.exists_original_frontier_disk_surgery_product s hR he hTR hd p hp hpi hpT hcontact
      pole hpoleT hpole isOpen_interior hpR hrOpen Q hQ hTQ
      (fun w hw => hcross w ((image_mono hprST) hw))
  obtain ⟨K,P,a,q,hm,har,had,hcover,caps,hdis,houtside,hNR,b,hnB⟩ :=
    s.exists_prescribed_nonbounding_surgery hR he hSR hn rho hρ hρi hρR hρS
  let N : Bool → Set X := fun c => s.map '' a c ∪ P.capDisk c
  have hcapT (c : Bool) : Disjoint (P.capDisk c) T := by
    simpa only [OriginalDiskProduct.capDisk,hm] using hρcaps c
  have hret (c : Bool) : (s.map '' a c) ∩ P.closedStrip = P.capRimSet c :=
    (har c).2.2.2.2.trans (har c).2.2.2.1
  have hPS : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim := by
    simpa only [hm] using hρS
  have hband : (P.map '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩ T = p '' r := by
    simpa only [hm] using hρband
  obtain ⟨_,_,hdelete,_,hstrip⟩ := P.positioned_circle_contact_geometry
    (fun c => s.map '' a c) had hret hcover hPS hcapT hband
  obtain ⟨n₀,L₀,hL₀i,hL₀,hL₀r⟩ := hd.exists_polygon_boundary
  have hrconn : IsConnected r := by
    obtain ⟨H⟩ := L₀.nonempty_boundary_homeomorph_circle hL₀ hL₀i
    exact hL₀r ▸ isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mpr inferInstance)
  have hprconn := hrconn.image p (hp.continuousOn.mono hd.1)
  have hprc : IsCompact (p '' r) := (hL₀r ▸ L₀.isCompact_boundary).image_of_continuousOn
    (hp.continuousOn.mono hd.1)
  have hQrimconn := hprconn.image Q (Q.continuousOn.mono (hprST.trans (inter_subset_right.trans hTQ)))
  have hQrimc := hprc.image_of_continuousOn
    (Q.continuousOn.mono (hprST.trans (inter_subset_right.trans hTQ)))
  have hQrem : IsCompact ((Q '' (S ∩ T)) \ Q '' (p '' r)) := by
    have heq := (Q.injOn.mono (inter_subset_right.trans hTQ) : InjOn Q (S ∩ T)).image_sdiff
      (t := p '' r)
    rw [inter_eq_right.mpr hprST] at heq
    rw [←heq]
    exact hrem.image_of_continuousOn (Q.continuousOn.mono
      (sdiff_subset.trans (inter_subset_right.trans hTQ)))
  obtain ⟨n,L,hLi,hL,hLrim⟩ :=
    HasDisjointPolygonPresentation.exists_polygon_of_isolated_connected_subset hpres
      (image_mono hprST) hQrimconn hQrimc.isClosed hQrem.isClosed
  have hLback : Q.symm '' L.boundary ℝ = p '' r := by
    rw [hLrim]
    exact Q.symm_image_image_of_subset_source (hprST.trans (inter_subset_right.trans hTQ))
  have hsingle (A : Set X) : (⋃ _ : Unit, A) = A := iUnion_const A
  have hupd (c : Bool) : Function.update (fun _ : Unit => S) () (N c) = fun _ => N c := by
    funext i
    cases i
    exact Function.update_self _ _ _
  have hfamily := sphere_frontier_family_decrease (fun _ : Unit => S) (fun _ => s)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) () Q t.isCompact.isClosed hTQ
    (by rw [hsingle]; exact hpres) L hLi hL (hLrim ▸ image_mono hprST)
    (by rw [hsingle,hLrim]; exact hQrem) N caps hdis
    (fun _ i hi => (hi (Subsingleton.elim i ())).elim) (by simpa only [hLback] using hdelete) b
  have hcount : HasDisjointPolygonPresentation (Q '' (N b ∩ T)) ∧
      Nat.card (ConnectedComponents ↥(Q '' (N b ∩ T))) <
        Nat.card (ConnectedComponents ↥(Q '' (S ∩ T))) ∧ N b ∩ T ⊆ S ∩ T := by
    obtain ⟨hp',hlt,hs'⟩ := hfamily
    rw [hupd,hsingle,hsingle] at hlt
    exact ⟨by simpa only [hupd,hsingle] using hp',hlt,
      by simpa only [hupd,hsingle] using hs'⟩
  have hNsub (c : Bool) : N c ⊆ S ∪ P.closedStrip := by
    rintro x (hx | hx)
    · apply Or.inl
      apply hcover.subset
      cases c
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl hx)
    · right
      apply P.endDisks_subset_closedStrip
      rw [P.endDisks_eq_capDisks]
      cases c
      · exact Or.inl hx
      · exact Or.inr hx
  have hNlevel (c : Bool) : Disjoint (N c ∩ T) P.closedStrip := by
    apply disjoint_left.mpr
    rintro x ⟨hx,hxT⟩ hxP
    rcases hx with hx | hx
    · exact disjoint_left.mp (hcapT c) (P.capRimSet_subset_capDisk c ((hret c).subset ⟨hx,hxP⟩)) hxT
    · exact disjoint_left.mp (hcapT c) hx hxT
  obtain ⟨V,hV,hNV,hagree⟩ := sphere_family_open_germ_after_exchange
    (fun _ : Unit => S) () (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    N (fun c => (caps c).isCompact.isClosed) hdis P.closedStrip T hstrip.isClosed
    (fun i hi => (hi (Subsingleton.elim i ())).elim) houtside hNsub hNlevel b
  simp only [hupd,hsingle] at hNV hagree
  exact ⟨N b,caps b,hNR b,hnB,hcount.1,hcount.2.2,hcount.2.1,V,hV,hNV,hagree,
    frontier_crossing_charts_of_open_agreement Q hTQ hV hNV hagree hcross⟩

end PoincareConjecture.M76
