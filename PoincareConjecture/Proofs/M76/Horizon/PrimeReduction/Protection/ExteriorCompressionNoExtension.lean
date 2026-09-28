import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCrossingEssentiality

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem Dehn.squareRimLoop_class_eq_one_of_extension
    {Y : Type*} [TopologicalSpace Y] (rim : C(Q2, Y))
    (F : C(D2, Y))
    (hF : ∀ x : Q2, F ⟨x, sphere_subset_closedBall x.property⟩ = rim x) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map rim.continuous)) = 1 := by
  let : ContractibleSpace D2 := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self (by norm_num)⟩
  let inclusion : C(Q2, D2) :=
    ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hcomp : F.comp inclusion = rim := by ext x; exact hF x
  subst rim
  have hnull := (SimplyConnectedSpace.paths_homotopic
    (squareRimLoop.map inclusion.continuous)
    (Path.refl (inclusion squareRimBase))).map F
  have hpath : (squareRimLoop.map inclusion.continuous).map F.continuous =
      squareRimLoop.map (F.comp inclusion).continuous := by ext t; rfl
  have href : (Path.refl (inclusion squareRimBase)).map F.continuous =
      Path.refl ((F.comp inclusion) squareRimBase) := by ext t; rfl
  rw [hpath, href] at hnull
  have hh : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (squareRimLoop.map (F.comp inclusion).continuous)) = 1 :=
    Path.Homotopic.Quotient.eq.mpr hnull
  exact hh

theorem HamiltonMarkedProtectedBall.exists_original_exterior_essential_disk_with_no_extension
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ (j : V2 → LatticeHandleAmbient ι κ L) (rim : C(Q2, frontier E)),
      PolyhedralPLInCharts e j D2 ∧ Topology.IsEmbedding (fun x : D2 => j x) ∧
      MapsTo j D2 E ∧ (∀ x : Q2, j x = (rim x : LatticeHandleAmbient ι κ L)) ∧
      (∀ x : D2, j x ∈ frontier E ↔ x.val ∈ Q2) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 ∧
      ¬ ∃ F : C(D2, frontier E),
        ∀ x : Q2, F ⟨x, sphere_subset_closedBall x.property⟩ = rim x := by
  obtain ⟨j, rim, hj, hji, hjE, hrim, hproper, hessential⟩ :=
    b.exists_original_exterior_essential_disk he hdim hi
  refine ⟨j, rim, hj, hji, hjE, hrim, hproper, hessential, ?_⟩
  rintro ⟨F, hF⟩
  exact hessential (Dehn.squareRimLoop_class_eq_one_of_extension rim F hF)

end PoincareConjecture.M76
