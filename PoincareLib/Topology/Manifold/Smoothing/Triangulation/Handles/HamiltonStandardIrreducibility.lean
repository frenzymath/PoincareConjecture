import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Coverings.HamiltonStandardBallLift
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonStandardQuotientPL
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonStandardBoundaryAtlas
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallNormalization

/-!
# PL irreducibility of the actual marked standard handle torus

The lifted Alexander ball descends injectively through the same lattice
quotient. Its complete finite PL cube parametrization has the original
sphere as its exact boundary. This proves the standard target-side
irreducibility required by Hamilton's named rigidity input, without any
Brown, Wall, Dehn, prime or rigidity hypothesis. See derivation340.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
  {α : Type*}
  {d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {S : Set (LatticeHandleAmbient ι κ L)}

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ L
local notation "pi" => (fun x : V =>
  (Prod.fst x, (QuotientAddGroup.mk (Prod.snd x) : (κ → ℝ) ⧸ L.toAddSubgroup)))

/-- The actual sphere in the marked standard handle bounds a chartwise
PL ball in that same atlas, with the entire original sphere as its
specified boundary. The quotient is proved injective on the full lifted
ball before descent. See Hamilton pp.66--67 and derivation340. -/
theorem ChartwisePLSphere.exists_standard_lattice_ball
    (s : ChartwisePLSphere d S) (hd : StandardLatticeHandleAtlas ι κ L d)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ latticeHandleDomain ι κ L) :
    ∃ D : Set W, D ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall d D S) := by
  obtain ⟨B, T, hB, hinj, hTS, hBR⟩ :=
    s.exists_standard_lattice_ball_lift ι κ L hd hdim hSR
  let D : Set W := pi '' B
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let q0 : B → D := fun x => ⟨pi x, mem_image_of_mem pi x.property⟩
  have hqcont : Continuous q0 :=
    ((continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd)).comp
      continuous_subtype_val).subtype_mk _
  have hqinj : Function.Injective q0 := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val hxy))
  have hqsurj : Function.Surjective q0 := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let q : B ≃ₜ D :=
    (hqcont.isClosedEmbedding hqinj).isEmbedding.toHomeomorphOfSurjective hqsurj
  let c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨b, hb, hboundary⟩ := hB.exists_cube_chart c
  obtain ⟨f, hf, hfeq⟩ := hb.symm
  have hSboundary (y : B) : pi y ∈ S ↔ (y : V) ∈ T := by
    rw [← hTS]
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact hinj (hB.1 hz) y.property hzy ▸ hz
    · intro hy
      exact mem_image_of_mem pi hy
  have hPL : PolyhedralPLInCharts d (pi ∘ f) (closedBall (0 : Fin 3 → ℝ) 1) := by
    let cSplit := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ
      (fun _ => ℝ)).symm.toContinuousAffineEquiv
    exact hd.polyhedralPL_projection (hf.postcomp cSplit.toContinuousAffineMap)
  refine ⟨D, ?_, ⟨{
    boundary_subset := ?_
    parametrization := b.symm.trans q
    map := pi ∘ f
    map_eq := ?_
    piecewiseAffine := hPL
    boundary_eq := ?_
  }⟩⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨(hBR hx).1, mem_univ _⟩
  · rw [← hTS]
    exact image_mono hB.1
  · intro x
    change pi (f x) = pi (b.symm x)
    exact congrArg pi (hfeq x).symm
  · intro x
    change pi (b.symm x) ∈ S ↔ (x : Fin 3 → ℝ) ∈ sphere (0 : Fin 3 → ℝ) 1
    rw [hSboundary, hboundary, b.apply_symm_apply, frontier_closedBall _ one_ne_zero]

/-- The marked standard handle atlas is PL irreducible. The assertion
uses the same lattice, bounded coordinates and original sphere maps.
Its proof depends only on the proved Alexander theorem and covering
geometry, not on any of Hamilton's named external inputs. See derivation340. -/
theorem StandardLatticeHandleAtlas.isPLIrreducible
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (hdim : Fintype.card ι + Fintype.card κ = 3) :
    IsPLIrreducible d (latticeHandleDomain ι κ L) := by
  refine ⟨hd.domain, ?_⟩
  intro S hS ⟨s⟩
  exact s.exists_standard_lattice_ball ι κ L hd hdim (hS.trans interior_subset)

/-- The exact marked lattice handle has an actual standard irreducible
PL atlas, including all boundary corners. This closes the target-atlas
and target-irreducibility obligations of the named rigidity input.
See Hamilton pp.64--67 and derivations339--340. -/
theorem exists_standard_irreducible_lattice_handle_atlas
    (hdim : Fintype.card ι + Fintype.card κ = 3) :
    ∃ d : V → OpenPartialHomeomorph W (Fin 3 → ℝ),
      StandardLatticeHandleAtlas ι κ L d ∧
        IsPLIrreducible d (latticeHandleDomain ι κ L) := by
  obtain ⟨d, hd⟩ := exists_standard_lattice_handle_atlas ι κ L hdim
  exact ⟨d, hd, hd.isPLIrreducible ι κ L hdim⟩

end PoincareMT.M76
