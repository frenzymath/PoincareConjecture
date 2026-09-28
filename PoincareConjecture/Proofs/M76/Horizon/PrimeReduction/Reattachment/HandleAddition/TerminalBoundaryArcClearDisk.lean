import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcCoreExclusion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcDiskRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ExteriorFrontierConnected
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

theorem HamiltonMarkedProtectedBall.exists_original_terminal_polygon_disk_with_clearance
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p Ann) (hpi : InjOn p Ann)
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
    (hf : PolyhedralPLInCharts e f A) (hfi : InjOn f A)
    (hS : f '' A ∩ S = f '' C)
    (hF : f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U)
    (hPS : p '' P.boundary ℝ ⊆ S)
    (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ) (hcd : c ≠ d)
    (h0 : f u0 = p c) (h1 : f u1 = p d)
    (hinter : f '' U ∩ p '' P.boundary ℝ = {f u0,f u1}) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ j : (Fin 2 → ℝ) → LatticeHandleAmbient ι κ L,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 ⊆ frontier E ∧
        (j '' sphere 0 1 = f '' U ∪ p '' V ∨
         j '' sphere 0 1 = f '' U ∪ p '' W) ∧
        Disjoint (j '' (closedBall 0 1 \ sphere 0 1)) (p '' P.boundary ℝ) ∧
        ∀ (m : ℕ) (Q : Polygon P2 (m+3)), Q.HasSimplicialEdges →
          Function.Injective Q →
          (∀ x ∈ Q.boundary ℝ,-1 < depth 8 x ∧ depth 8 x < 1) →
          Dehn.annulusSquare 8 1 ⊆ Q.inside →
          Disjoint (j '' sphere 0 1) (p '' Q.boundary ℝ) →
          Disjoint (j '' closedBall 0 1) (p '' Q.boundary ℝ) := by
  classical
  intro E
  let X := LatticeHandleAmbient ι κ L
  have heE : PLDomain e E := b.plDomain_closed_complement he hdim hi
  let : ConnectedSpace (frontier E) :=
    isConnected_iff_connectedSpace.mp (b.isConnected_closed_complement_frontier he hdim hi)
  obtain ⟨V,W,hV,hW,hVW,hVWint,O,hO,hK,hsc,hproper,hrim,hdis,hexclude⟩ :=
    b.exists_original_terminal_polygon_region_with_core_exclusion he hdim hi p hp.continuousOn hpi
      hfront hfull hint hends P hP hPi hdepth hencl s hA hU hC hUC hu
      hf.continuousOn hfi hS hF hPS hc hd hcd h0 h1 hinter
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hPAnn : P.boundary ℝ ⊆ Ann := fun z hz =>
    mem_squareAnnulus_iff_depth.mpr ⟨(hdepth z hz).1.le,(hdepth z hz).2.le⟩
  have finish (Z : Set P2) (hZ : IsFinitePLBallPair ℝ Z {c,d})
      (hZP : Z ⊆ P.boundary ℝ)
      (hZrim : (Subtype.val : frontier E → X) '' frontier O = f '' U ∪ p '' Z) :
      ∃ j : (Fin 2 → ℝ) → X,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 ⊆ frontier E ∧
        j '' sphere 0 1 = f '' U ∪ p '' Z ∧
        Disjoint (j '' (closedBall 0 1 \ sphere 0 1)) (p '' P.boundary ℝ) ∧
        ∀ (m : ℕ) (Q : Polygon P2 (m+3)), Q.HasSimplicialEdges →
          Function.Injective Q →
          (∀ x ∈ Q.boundary ℝ,-1 < depth 8 x ∧ depth 8 x < 1) →
          Dehn.annulusSquare 8 1 ⊆ Q.inside →
          Disjoint (j '' sphere 0 1) (p '' Q.boundary ℝ) →
          Disjoint (j '' closedBall 0 1) (p '' Q.boundary ℝ) := by
    have hInt : f '' U ∩ p '' Z = {f u0,f u1} := by
      apply Subset.antisymm
      · exact (inter_subset_inter_right _ (image_mono hZP)).trans hinter.subset
      · intro x hx
        rcases mem_insert_iff.mp hx with rfl | hx
        · exact ⟨mem_image_of_mem f (hU.1 (by simp)),
            ⟨c,hZ.1 (by simp),h0.symm⟩⟩
        · rw [mem_singleton_iff] at hx
          subst x
          exact ⟨mem_image_of_mem f (hU.1 (by simp)),
            ⟨d,hZ.1 (by simp),h1.symm⟩⟩
    obtain ⟨H,j,hj,hji,hjH,himage,hjr⟩ :=
      heE.exists_original_disk_of_two_arc_boundary_region hU hZ hu hcd
        (by
          obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hU
          exact hKs ▸ hf.restrict_finite K hK (hKs.subset.trans hUA))
        (by
          obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hZ
          exact hKs ▸ hp.restrict_finite K hK (hKs.subset.trans (hZP.trans hPAnn)))
        (hfi.mono hUA)
        (hpi.mono (hZP.trans hPAnn)) h0 h1 hInt hO hK hsc hproper hZrim
    have hDfront : j '' closedBall 0 1 ⊆ frontier E := by
      rw [himage]
      rintro _ ⟨z,_,rfl⟩
      exact z.property
    have hRim : j '' sphere 0 1 = f '' U ∪ p '' Z := by
      apply Subset.antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact (hjr ⟨z,sphere_subset_closedBall hz⟩).mpr hz
      · intro x hx
        have hxK : x ∈ (Subtype.val : frontier E → X) '' closure O :=
          image_mono frontier_subset_closure (hZrim.symm.subset hx)
        rw [←himage] at hxK
        obtain ⟨z,hz,rfl⟩ := hxK
        exact ⟨z,(hjr ⟨z,hz⟩).mp hx,rfl⟩
    refine ⟨j,?_,?_,hDfront,hRim,?_,?_⟩
    · exact hj
    · intro x hx y hy hh
      exact congrArg Subtype.val (hji.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hh)
    · apply disjoint_left.mpr
      rintro x ⟨z,hz,rfl⟩ hxcore
      have hzk := himage.subset (mem_image_of_mem j hz.1)
      obtain ⟨y,hy,hyeq⟩ := hzk
      have hyn : y ∉ frontier O := by
        intro hyr
        have hzrim := hZrim.subset (mem_image_of_mem Subtype.val hyr)
        rw [hyeq] at hzrim
        exact hz.2 ((hjr ⟨z,hz.1⟩).mp hzrim)
      have hyO : y ∈ O := by
        have hh : y ∈ closure O \ frontier O := ⟨hy,hyn⟩
        rwa [closure_sdiff_frontier,hO.interior_eq] at hh
      exact disjoint_left.mp hdis ⟨y,hyO,hyeq⟩ hxcore
    · intro m Q hQ hQi hQdepth hQencl hQr
      let jF : C(closedBall (0 : Fin 2 → ℝ) 1,frontier E) :=
        ⟨fun z => ⟨j z,hDfront (mem_image_of_mem j z.property)⟩,
          hj.continuousOn.domRestrict.subtype_mk _⟩
      have hjiF : Function.Injective jF := fun x y hh =>
        hji.injective (congrArg Subtype.val hh)
      have hjFO : range jF ⊆ closure O := by
        rintro _ ⟨z,rfl⟩
        obtain ⟨y,hy,hyz⟩ := himage.subset (mem_image_of_mem j z.property)
        exact (Subtype.ext hyz : y = jF z) ▸ hy
      have hnotsub : ¬p '' Q.boundary ℝ ⊆ Subtype.val '' closure O := by
        intro hsub
        apply hexclude jF hjiF hjFO m Q hQ hQi hQdepth hQencl
        intro x hx
        obtain ⟨z,hz,hzx⟩ := himage.symm.subset (hsub hx)
        exact ⟨jF ⟨z,hz⟩,mem_range_self _,hzx⟩
      have hQAnn : Q.boundary ℝ ⊆ Ann := fun z hz =>
        mem_squareAnnulus_iff_depth.mpr ⟨(hQdepth z hz).1.le,(hQdepth z hz).2.le⟩
      have hT : p '' Ann = E ∩ D :=
        (marked_annular_image_eq_frontier_closure p hp.continuousOn hfront hfull hint hends).trans
          (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
            b.ball.closure_interior).symm
      have hTF : p '' Ann ⊆ frontier E := by
        obtain ⟨_,_,_,hcontact,_,_,hfrontE⟩ := b.closed_complement_geometry he hdim hi
        intro x hx
        rw [hfrontE,←hcontact]
        exact Or.inl (hT.subset hx)
      rw [himage]
      apply disjoint_closed_region_of_preconnected_not_subset hO
        ((Q.isConnected_boundary hQ hQi).isPreconnected.image p (hp.continuousOn.mono hQAnn))
        ((image_mono hQAnn).trans hTF) ?_ hnotsub
      rw [hZrim,←hRim]
      exact hQr
  refine ⟨V,W,hV,hW,hVW,hVWint,?_⟩
  rcases hrim with hrim | hrim
  · obtain ⟨j,hj,hji,hfrontj,hjr,hdisj,hclear⟩ :=
      finish V hV (fun z hz => hVW.subset (Or.inl hz)) hrim
    exact ⟨j,hj,hji,hfrontj,Or.inl hjr,hdisj,hclear⟩
  · obtain ⟨j,hj,hji,hfrontj,hjr,hdisj,hclear⟩ :=
      finish W hW (fun z hz => hVW.subset (Or.inr hz)) hrim
    exact ⟨j,hj,hji,hfrontj,Or.inr hjr,hdisj,hclear⟩

end PoincareConjecture.M76

