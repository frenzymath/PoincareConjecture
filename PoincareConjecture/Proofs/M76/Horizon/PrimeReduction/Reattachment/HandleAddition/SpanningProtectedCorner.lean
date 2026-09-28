import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBigonCornerDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBigonFrontierCollar

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.plDomain_of_compatible_cover
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D T : Set X}
    (b : ChartwisePLBall e D T)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source) : PLDomain e D := by
  obtain ⟨s⟩ := b.nonempty_boundarySphere
  apply s.plDomain_of_unitBallPair b.isCompact b.frontier_eq _ hcompat hcover
  refine ⟨b.boundary_subset,b.parametrization.symm,?_⟩
  intro x
  simpa only [b.parametrization.apply_symm_apply] using b.boundary_eq (b.parametrization.symm x)

theorem HamiltonMarkedProtectedBall.frontier_complement_iff_interior
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    {x : LatticeHandleAmbient ι κ L} (hx : x ∈ interior (latticeHandleDomain ι κ L)) :
    x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ x ∈ frontier D := by
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨_,_,_,_,hiE,_,_⟩ := b.closed_complement_geometry he hdim hi
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hy hz => hy.2 (interior_subset hz)) isOpen_interior.isClosed_compl
  constructor
  · intro h
    have hxE := isClosed_closure.frontier_subset h
    have hxD : x ∈ D := by
      by_contra hn
      exact h.2 (hiE.symm ▸ And.intro hx hn)
    exact ⟨subset_closure hxD,hout hxE⟩
  · intro h
    have hc := he.closed_complement_contact b.ball.isCompact.isClosed
      b.subset_domain b.ball.closure_interior
    have hxE : x ∈ E := (hc.symm.subset (subset_closure ⟨h,hx⟩)).1
    refine ⟨subset_closure hxE,?_⟩
    intro hxi
    exact (hiE.subset hxi).2 (b.ball.isCompact.isClosed.frontier_subset h)

theorem HamiltonMarkedProtectedBall.plDomain_protected_corner
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hW : PLDomain e W) (hWS : frontier W = S)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hcross : ∀ x ∈ S ∩ frontier (closure (latticeHandleDomain ι κ L \ D)),
      ∃ H : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ H y 0 = 0) :
    IsCompact (D ∩ W) ∧ PLDomain e (D ∩ W) ∧
      frontier (D ∩ W) = (D ∩ W) ∩ (frontier D ∪ S) := by
  have hD := b.ball.plDomain_of_compatible_cover he.compatible he.cover
  have hDW : PLDomain e (D ∩ W) := by
    apply hD.inter_of_transverse_frontiers hW
    intro x hx
    have hxS : x ∈ S := hWS ▸ hx.2
    have hxR := hSR hxS
    have hxE := (b.frontier_complement_iff_interior he hdim hi hxR).mpr hx.1
    obtain ⟨H,hxH,hHz,hHe,hHS,hHE⟩ := hcross x ⟨hxS,hxE⟩
    let G := H.restrOpen (interior (latticeHandleDomain ι κ L)) isOpen_interior
    refine ⟨G,⟨hxH,hxR⟩,hHz,?_,?_,?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hHe i) isOpen_interior
    · intro y hy
      exact (b.frontier_complement_iff_interior he hdim hi hy.2).symm.trans (hHE y hy.1)
    · intro y hy
      exact hWS ▸ hHS y hy.1
  refine ⟨b.ball.isCompact.inter_right hW.closed,hDW,?_⟩
  apply Subset.antisymm
  · intro x hx
    refine ⟨hDW.closed.frontier_subset hx,?_⟩
    rcases (frontier_inter_subset D W) hx with h | h
    · exact Or.inl h.1
    · exact Or.inr (hWS ▸ h.2)
  · rintro x ⟨hx,hd | hs⟩
    · exact ⟨subset_closure hx,fun h => hd.2 (interior_mono inter_subset_left h)⟩
    · exact ⟨subset_closure hx,fun h => (hWS.symm ▸ hs).2 (interior_mono inter_subset_right h)⟩

theorem HamiltonMarkedProtectedBall.exists_original_bigon_paired_corners
    {ι κ α F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let X := LatticeHandleAmbient ι κ L
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
      {d U C : Set F} (_hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C))
      {f : F → X} (_hf : PolyhedralPLInCharts e f d) (_hfi : InjOn f d)
      (_hfE : MapsTo f d E)
      (_hfront : f '' d ∩ frontier E = f '' U)
      (_hsphere : f '' d ∩ S = f '' C),
    ∃ W : Set X, PLDomain e W ∧ frontier W = S ∧
      IsCompact (E ∩ W) ∧ PLDomain e (E ∩ W) ∧ MapsTo f d (E ∩ W) ∧
      (∀ z ∈ d, f z ∈ frontier (E ∩ W) ↔ z ∈ U ∪ C) ∧
      frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S) ∧
      IsCompact (D ∩ W) ∧ PLDomain e (D ∩ W) ∧
      frontier (D ∩ W) = (D ∩ W) ∩ (frontier D ∪ S) := by
  intro X E hcross d U C hd f hf hfi hfE hfront hsphere
  have hE := (b.closed_complement_geometry he hdim hi).1
  have heE := b.plDomain_closed_complement he hdim hi
  obtain ⟨Q,hQ,hQS,hpair,hq,hqc,hQR⟩ := s.exists_lattice_ball_domains L he hdim hSR
  have havoid : Disjoint (f '' (d \ (U ∪ C))) (frontier Q) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    obtain ⟨y,hy,heq⟩ := hsphere.subset ⟨⟨z,hz.1,rfl⟩,hQS ▸ hx⟩
    exact hz.2 (Or.inr (hfi (hd.1 (Or.inr hy)) hz.1 heq ▸ hy))
  obtain ⟨W,hW,hWS,hfW,hfWi⟩ :
      ∃ W : Set X, PLDomain e W ∧ frontier W = S ∧ f '' d ⊆ W ∧
        f '' (d \ (U ∪ C)) ⊆ interior W := by
    rcases finitePLBallPair_image_closed_side hd hf.continuousOn hQ.isClosed
        hq.closure_interior havoid with hin | hout
    · exact ⟨Q,hq,hQS,hin⟩
    · exact ⟨(interior Q)ᶜ,hqc,hq.frontier_closed_exterior.trans hQS,hout⟩
  have heN : PLDomain e (E ∩ W) := by
    apply heE.inter_of_transverse_frontiers hW
    intro x hx
    obtain ⟨H,hxH,hHz,hHe,hHS,hHE⟩ := hcross x ⟨hWS ▸ hx.2,hx.1⟩
    exact ⟨H,hxH,hHz,hHe,hHE,fun y hy => hWS ▸ hHS y hy⟩
  have hfN : MapsTo f d (E ∩ W) := fun z hz => ⟨hfE hz,hfW ⟨z,hz,rfl⟩⟩
  refine ⟨W,hW,hWS,hE.inter_right hW.closed,heN,hfN,?_,?_,
    b.plDomain_protected_corner he hdim hi hW hWS hSR hcross⟩
  · intro z hz
    constructor
    · intro hn
      by_contra hzq
      have hzE : f z ∈ interior E := by
        apply (mem_interior_iff_notMem_frontier (hfE hz)).mpr
        intro hx
        obtain ⟨y,hy,heq⟩ := hfront.subset ⟨⟨z,hz,rfl⟩,hx⟩
        exact hzq (Or.inl (hfi (hd.1 (Or.inl hy)) hz heq ▸ hy))
      exact hn.2 (by rw [interior_inter]; exact ⟨hzE,hfWi ⟨z,⟨hz,hzq⟩,rfl⟩⟩)
    · intro hzq
      refine ⟨subset_closure (hfN hz),?_⟩
      intro hint
      rcases hzq with hu | hc
      · exact (hfront.symm.subset ⟨z,hu,rfl⟩).2.2 (interior_mono inter_subset_left hint)
      · exact (hWS.symm ▸ (hsphere.symm.subset ⟨z,hc,rfl⟩).2).2
          (interior_mono inter_subset_right hint)
  · apply Subset.antisymm
    · intro x hx
      refine ⟨heN.closed.frontier_subset hx,?_⟩
      rcases (frontier_inter_subset E W) hx with h | h
      · exact Or.inl h.1
      · exact Or.inr (hWS ▸ h.2)
    · rintro x ⟨hx,hxf⟩
      refine ⟨subset_closure hx,?_⟩
      intro hint
      rcases hxf with hE | hS
      · exact hE.2 (interior_mono inter_subset_left hint)
      · exact (hWS.symm ▸ hS).2 (interior_mono inter_subset_right hint)

theorem HamiltonMarkedProtectedBall.exists_original_protected_side_cap
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hW : PLDomain e W) (hWS : frontier W = S)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    let Disk := closedBall (0 : Fin 2 → ℝ) 1
    let Rim := sphere (0 : Fin 2 → ℝ) 1
    let I := Icc (0 : ℝ) 1
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
      {j : (Fin 2 → ℝ) → X} (_hj : PolyhedralPLInCharts e j Disk)
      (_hji : InjOn j Disk) (_hjF : MapsTo j Disk (frontier E))
      (_hjW : MapsTo j Disk W) (_hjR : MapsTo j Disk (interior R))
      {O : Set X} (_hO : IsOpen O) (_hjO : j '' Disk ⊆ O),
    ∃ k : (Fin 2 → ℝ) × ℝ → X,
      PolyhedralPLInCharts e k (Disk ×ˢ I) ∧ InjOn k (Disk ×ˢ I) ∧
      MapsTo k (Disk ×ˢ I) (D ∩ W) ∧ MapsTo k (Disk ×ˢ I) (O ∩ interior R) ∧
      (∀ x ∈ Disk, k (x,0) = j x) ∧
      (∀ z ∈ Disk ×ˢ I, k z ∈ E ↔ z.2 = 0) ∧
      k '' (Disk ×ˢ I) ∩ E = j '' Disk ∧
      k '' (Disk ×ˢ I) ∩ S = (j '' Disk) ∩ S ∧
      Nonempty (ChartwisePLBall e (k '' (Disk ×ˢ I))
        (k '' ((Rim ×ˢ I) ∪ (Disk ×ˢ ({0,1} : Set ℝ))))) := by
  intro X R E Disk Rim I hcross j hj hji hjF hjW hjR O hO hjO
  obtain ⟨hN,heN,hNf⟩ := b.plDomain_protected_corner he hdim hi hW hWS hSR hcross
  have hjN : MapsTo j Disk (frontier (D ∩ W)) := by
    intro z hz
    have hzD := (b.frontier_complement_iff_interior he hdim hi (hjR hz)).mp (hjF hz)
    rw [hNf]
    exact ⟨⟨b.ball.isCompact.isClosed.frontier_subset hzD,hjW hz⟩,Or.inl hzD⟩
  obtain ⟨k,hk,hki,hkN,hkO,hk0,hkfront,hkcontact,hball⟩ :=
    exists_original_frontier_disk_inward_block hN heN hj hji hjN
      (hO.inter isOpen_interior) (subset_inter hjO (image_subset_iff.mpr hjR))
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hy hz => hy.2 (interior_subset hz)) isOpen_interior.isClosed_compl
  have hkE (z) (hz : z ∈ Disk ×ˢ I) : k z ∈ E ↔ z.2 = 0 := by
    constructor
    · intro hzE
      apply (hkfront z hz).mp
      rw [hNf]
      exact ⟨hkN hz,Or.inl ⟨subset_closure (hkN hz).1,hout hzE⟩⟩
    · intro ht
      have hzeq : z = (z.1,0) := Prod.ext rfl ht
      rw [hzeq,hk0 z.1 hz.1]
      exact isClosed_closure.frontier_subset (hjF hz.1)
  have hbase : j '' Disk ⊆ k '' (Disk ×ˢ I) := by
    rintro x ⟨z,hz,rfl⟩
    exact ⟨(z,0),⟨hz,by norm_num [I]⟩,hk0 z hz⟩
  refine ⟨k,hk,hki,hkN,hkO,hk0,hkE,?_,?_,hball⟩
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hx⟩
      have ht := (hkE z hz).mp hx
      have hzeq : z = (z.1,0) := Prod.ext rfl ht
      exact ⟨z.1,hz.1,(hk0 z.1 hz.1).symm.trans (congrArg k hzeq.symm)⟩
    · exact fun x hx => ⟨hbase hx,isClosed_closure.frontier_subset (image_subset_iff.mpr hjF hx)⟩
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hx⟩
      have hfr : k z ∈ frontier (D ∩ W) := hNf.symm ▸ And.intro (hkN hz) (Or.inr hx)
      exact ⟨hkcontact.subset ⟨⟨z,hz,rfl⟩,hfr⟩,hx⟩
    · exact inter_subset_inter_left S hbase

end PoincareConjecture.M76
