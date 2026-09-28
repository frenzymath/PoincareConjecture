import PoincareConjecture.Proofs.M76.Rigidity.MeridianBand
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L


def hamiltonMeridianOpenBand : Set X :=
  hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-1 : ℝ) 1)

theorem hamiltonMeridianOpenBand_subset_frontier :
    hamiltonMeridianOpenBand ⊆ frontier R := by
  rintro y ⟨z, hz, rfl⟩
  exact mapsTo_hamiltonMeridianBand_frontier ⟨hz.1, hz.2.1.le, hz.2.2.le⟩


def hamiltonMeridianOpenBandProjection : C(hamiltonMeridianOpenBand, Q) := by
  have hfirst (y : hamiltonMeridianOpenBand) : (y : X).1 ∈ Q := by
    obtain ⟨z, hz, hzy⟩ := y.property
    exact (congrArg Prod.fst hzy) ▸ hz.1
  exact ⟨fun y => ⟨(y : X).1, hfirst y⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk hfirst⟩




theorem exists_source_meridian_open_band_disk
    {α : Type*} (e : α → OpenPartialHomeomorph X V3) (he : PLDomain e R) :
    ∃ (j : V2 → X) (rim : C(Q, hamiltonMeridianOpenBand)),
      PolyhedralPLInCharts e j D ∧
      Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D R ∧
      (∀ x : Q, j x = (rim x : X)) ∧
      (∀ x : D, j x ∈ frontier R ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map rim.continuous).map
          hamiltonMeridianOpenBandProjection.continuous)) ≠ 1 := by
  let : DiscreteTopology (hamiltonLowerPeriodLattice (Fin 1)).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (hamiltonLowerPeriodLattice (Fin 1)))
  let : T2Space X := inferInstance
  let f : C(D, R) :=
    ⟨fun x => ⟨((x : V2), 0), x.property, mem_univ _⟩,
      (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩
  have hmark (x : Q) : hamiltonStandardMeridianMap L x ∈ hamiltonMeridianOpenBand := by
    exact ⟨((x : V2), 0), ⟨x.property, by norm_num, by norm_num⟩, rfl⟩
  let gamma : C(Q, hamiltonMeridianOpenBand) :=
    ⟨fun x => ⟨hamiltonStandardMeridianMap L x, hmark x⟩,
      (continuous_subtype_val.prodMk continuous_const).subtype_mk hmark⟩
  have hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((Dehn.squareRimLoop.map gamma.continuous).map
        hamiltonMeridianOpenBandProjection.continuous)) ≠ 1 :=
    Dehn.squareRimLoop_class_ne_one
  exact Dehn.exists_marked_boundary_disk_with_essential_image e R he
    hamiltonMeridianOpenBand hamiltonMeridianOpenBand_subset_frontier
    isOpen_hamiltonMeridianBand_image f gamma (fun _ => rfl)
    hamiltonMeridianOpenBandProjection hessential

end PoincareConjecture.M76
