import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalDiskSurfaceComponents

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem HamiltonMarkedProtectedBall.exists_minimal_essential_exterior_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ closure (latticeHandleDomain ι κ L \ D))
    (hcross : ∀ x ∈ S ∩ frontier (closure (latticeHandleDomain ι κ L \ D)),
      ∃ Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
        x ∈ Q.source ∧ Q x = 0 ∧
        (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source, y ∈ S ↔ Q y 1 = 0) ∧
        ∀ y ∈ Q.source, y ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ Q y 0 = 0) :
    let X := LatticeHandleAmbient ι κ L
    let E := closure (latticeHandleDomain ι κ L \ D)
    let disks : Set (V2 → X) := {j |
      PolyhedralPLInCharts e j D2 ∧ Topology.IsEmbedding (fun x : D2 => j x) ∧
      MapsTo j D2 E ∧ (∀ x : D2, j x ∈ frontier E ↔ (x : V2) ∈ Q2) ∧
      (¬ ∃ F : C(D2,frontier E), ∀ x : Q2,
        (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = j x) ∧
      (∀ y ∈ S ∩ frontier E, y ∈ j '' D2 →
        ∃ C : OriginalSurfacePairChart e (S ∩ E) (j '' D2) y true,
          (∀ v ∈ C.coordinates.source, C.chart.symm v ∈ E ↔ 0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source, C.chart.symm v ∈ frontier E ↔ (C.coordinates v).1.2 = 0) ∧
      ∀ y ∈ S ∩ interior E, y ∈ j '' D2 →
        Nonempty (OriginalSurfacePairChart e (S ∩ E) (j '' D2) y false)}
    ∃ j ∈ disks,
      (∀ k ∈ disks, Nat.card (ConnectedComponents ↥(D2 ∩ j ⁻¹' S)) ≤
        Nat.card (ConnectedComponents ↥(D2 ∩ k ⁻¹' S))) ∧
      Nonempty (SurfaceIntersectionComponents K.space D2 p j Q2) := by
  classical
  intro X E disks
  have heE := b.plDomain_closed_complement he hdim hi
  have hex : ∃ n : ℕ, ∃ j ∈ disks,
      Nat.card (ConnectedComponents ↥(D2 ∩ j ⁻¹' S)) = n := by
    obtain ⟨j,P,hopen,hall⟩ := b.exists_replacement_exterior_essential_disk_product
      he hdim hi e heE
    obtain ⟨t,_,hboundary,hinterior,_⟩ := P.exists_regular_surface_contact_components
      s heE (fun x _ => heE.cover x) (hopen 1 (by norm_num) le_rfl).1
      K hK hp hpi hps hcross
    obtain ⟨hPL,hemb,hinto,hproper,_,hno⟩ := hall t
    refine ⟨_,P.slice t,⟨hPL,hemb,hinto,hproper,?_,hboundary,hinterior⟩,rfl⟩
    rintro ⟨F,hF⟩
    exact hno ⟨F,fun x => Subtype.ext (hF x)⟩
  obtain ⟨j,hj,hcount⟩ := Nat.find_spec hex
  refine ⟨j,hj,?_,?_⟩
  · intro k hk
    rw [hcount]
    exact Nat.find_min' hex ⟨k,hk,rfl⟩
  · obtain ⟨hPL,hemb,hinto,hproper,hno,hboundary,hinterior⟩ := hj
    obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
    have hjJ : PolyhedralPLInCharts e j J.space := hJs.symm ▸ hPL
    have hji : InjOn j J.space := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x,hJs.subset hx⟩)
        (a₂ := ⟨y,hJs.subset hy⟩) hxy)
    have hbc : ∀ y ∈ J.space ∩ Q2, j y ∈ p '' K.space →
        Nonempty (OriginalSurfacePairChart e (p '' K.space) (j '' J.space) (j y) true) := by
      intro y hy hyP
      obtain ⟨C,_,_⟩ := hboundary (j y)
        ⟨(hps.subset hyP).1,(hproper ⟨y,hJs.subset hy.1⟩).mpr hy.2⟩
        (mem_image_of_mem j (hJs.subset hy.1))
      simpa only [hps,hJs] using (show Nonempty
        (OriginalSurfacePairChart e (S ∩ E) (j '' D2) (j y) true) from ⟨C⟩)
    have hic : ∀ y ∈ J.space \ Q2, j y ∈ p '' K.space →
        Nonempty (OriginalSurfacePairChart e (p '' K.space) (j '' J.space) (j y) false) := by
      intro y hy hyP
      have hyD := hJs.subset hy.1
      have hyint : j y ∈ interior E :=
        (mem_interior_iff_notMem_frontier (hinto hyD)).mpr
          (fun h => hy.2 ((hproper ⟨y,hyD⟩).mp h))
      have hh := hinterior (j y) ⟨(hps.subset hyP).1,hyint⟩ (mem_image_of_mem j hyD)
      simpa only [hps,hJs] using hh
    have hh := nonempty_surface_intersection_components heE.compatible K J hK hJ
      hp hjJ hpi hji Q2 hbc hic
    simpa only [hJs] using hh

end PoincareConjecture.M76
