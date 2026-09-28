import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningProtectedCorner
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.RetainedDiskProduct



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_relative_protected_cap
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
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
      {j : V2 → X} (_hj : PolyhedralPLInCharts e j Disk)
      (_hji : InjOn j Disk) (_hjF : MapsTo j Disk (frontier E))
      (_hjW : MapsTo j Disk W) (_hjR : MapsTo j Disk (interior R))
      {O : Set X} (_hO : IsOpen O) (_hjO : j '' Disk ⊆ O),
    ∃ k : V2 × ℝ → X,
      PolyhedralPLInCharts e k (Disk ×ˢ J) ∧ InjOn k (Disk ×ˢ J) ∧
      MapsTo k (Disk ×ˢ J) (D ∩ W) ∧ MapsTo k (Disk ×ˢ J) (O ∩ interior R) ∧
      (∀ x ∈ Disk, k (x,0) = j x) ∧
      (∀ z ∈ Disk ×ˢ J, k z ∈ E ↔ z.2 = 0) ∧
      (∀ z ∈ Disk ×ˢ J, k z ∈ S ↔ j z.1 ∈ S) ∧
      k '' (Disk ×ˢ J) ∩ E = j '' Disk ∧
      Nonempty (ChartwisePLBall e (k '' (Disk ×ˢ J))
        (k '' ((Rim ×ˢ J) ∪ (Disk ×ˢ ({0,1} : Set ℝ))))) ∧
      ∃ (K : Set X) (s : Finset (D ∪ K : Set X))
        (P : RelativeFrontierDiskProduct e D W (O ∩ interior R) j K s), P.map = k := by
  intro X R E hcross j hj hji hjF hjW hjR O hO hjO
  have heD := b.ball.plDomain_of_compatible_cover he.compatible he.cover
  have hcrossD : ∀ x ∈ frontier D ∩ frontier W,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ frontier D ↔ H y 0 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier W ↔ H y 1 = 0 := by
    intro x hx
    have hxS : x ∈ S := hWS ▸ hx.2
    have hxR := hSR hxS
    have hxE := (b.frontier_complement_iff_interior he hdim hi hxR).mpr hx.1
    obtain ⟨H,hxH,hHz,hHe,hHS,hHE⟩ := hcross x ⟨hxS,hxE⟩
    let G := H.restrOpen (interior R) isOpen_interior
    refine ⟨G,⟨hxH,hxR⟩,hHz,?_,?_,?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hHe i) isOpen_interior
    · intro y hy
      exact (b.frontier_complement_iff_interior he hdim hi hy.2).symm.trans (hHE y hy.1)
    · intro y hy
      exact hWS ▸ hHS y hy.1
  have hjD : MapsTo j Disk (frontier D) := fun z hz =>
    (b.frontier_complement_iff_interior he hdim hi (hjR hz)).mp (hjF hz)
  obtain ⟨K,s,⟨P⟩⟩ :=
    exists_confined_relative_frontier_disk_collar_with_product e D W (O ∩ interior R) j
      b.ball.isCompact heD hW hcrossD
      hj hji hjD hjW (hO.inter isOpen_interior)
      (subset_inter hjO (image_subset_iff.mpr hjR))
  let k := P.map
  have hk0 : ∀ z ∈ Disk,k (z,0) = j z := P.map_central
  have hkDW : MapsTo k (Disk ×ˢ J) (D ∩ W) := fun z hz => (P.map_inside hz).1.1
  have hkO : MapsTo k (Disk ×ˢ J) (O ∩ interior R) := fun z hz => (P.map_inside hz).1.2
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hy hz => hy.2 (interior_subset hz)) isOpen_interior.isClosed_compl
  have hkE (z) (hz : z ∈ Disk ×ˢ J) : k z ∈ E ↔ z.2 = 0 := by
    constructor
    · intro hzE
      exact (P.map_frontier z hz).mp ⟨subset_closure (hkDW hz).1,hout hzE⟩
    · intro ht
      rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]
      exact isClosed_closure.frontier_subset (hjF hz.1)
  refine ⟨k,P.map_PL,P.map_injective,hkDW,hkO,P.map_central,hkE,?_,?_,?_,K,s,P,rfl⟩
  · intro z hz
    simpa only [hWS] using P.map_boundary z hz
  · ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hx⟩
      have ht := (hkE z hz).mp hx
      rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨(z,0),⟨hz,by norm_num⟩,P.map_central z hz⟩,
        isClosed_closure.frontier_subset (hjF hz)⟩
  · exact exists_chartwisePLBall_image
      ((isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
        (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)))
      (ContinuousLinearEquiv.ofFinrankEq (by simp)) P.map_PL subset_rfl P.map_injective

end PoincareConjecture.M76
