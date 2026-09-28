import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ExteriorCompressionNoExtension

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem HamiltonMarkedProtectedBall.exists_replacement_exterior_essential_disk
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (e' : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (he' : PLDomain e' (closure (latticeHandleDomain ι κ L \ D))) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ (j : V2 → LatticeHandleAmbient ι κ L) (rim : C(Q2, frontier E)),
      PolyhedralPLInCharts e' j D2 ∧ Topology.IsEmbedding (fun x : D2 => j x) ∧
      MapsTo j D2 E ∧ (∀ x : Q2, j x = (rim x : LatticeHandleAmbient ι κ L)) ∧
      (∀ x : D2, j x ∈ frontier E ↔ x.val ∈ Q2) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 ∧
      ¬ ∃ F : C(D2, frontier E),
        ∀ x : Q2, F ⟨x, sphere_subset_closedBall x.property⟩ = rim x := by
  dsimp only
  let E := closure (latticeHandleDomain ι κ L \ D)
  obtain ⟨j₀, rim₀, hj₀, hji₀, hjE₀, hrim₀, hproper₀, hessential₀⟩ :=
    b.exists_original_exterior_essential_disk he hdim hi
  let f : C(D2, E) :=
    ⟨fun x => ⟨j₀ x, hjE₀ x.property⟩, hji₀.continuous.subtype_mk _⟩
  let u : C(frontier E, frontier E) := ContinuousMap.id _
  have hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((Dehn.squareRimLoop.map rim₀.continuous).map u.continuous)) ≠ 1 := by
    have hid : (Dehn.squareRimLoop.map rim₀.continuous).map u.continuous =
        Dehn.squareRimLoop.map rim₀.continuous := by apply Path.ext; rfl
    rwa [hid]
  obtain ⟨j, rim, hj, hji, hjE, hrim, hproper, himage⟩ :=
    Dehn.exists_marked_boundary_disk_with_essential_image e' E he'
      (frontier E) subset_rfl
      (by simpa only [Subtype.coe_preimage_self] using
        (isOpen_univ : IsOpen (univ : Set (frontier E))))
      f rim₀ hrim₀ u hessential
  have hess : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
    have hid : (Dehn.squareRimLoop.map rim.continuous).map u.continuous =
        Dehn.squareRimLoop.map rim.continuous := by apply Path.ext; rfl
    rwa [hid] at himage
  refine ⟨j, rim, hj, hji, hjE, hrim, hproper, hess, ?_⟩
  rintro ⟨F, hF⟩
  exact hess (Dehn.squareRimLoop_class_eq_one_of_extension rim F hF)

end PoincareConjecture.M76
