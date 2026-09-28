import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Annulus.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.ChartImage
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable (L : Submodule ℤ V2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "pi" => hamiltonMarkedProjection (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L

def ambientShell : Set X :=
  univ ×ˢ ((QuotientAddGroup.mk : V2 → V2 ⧸ L.toAddSubgroup) ''
    {y : V2 | 1 < ‖y‖ ∧ ‖y‖ < 2})

theorem ambientShell_isOpen : IsOpen (ambientShell L) :=
  isOpen_univ.prod (QuotientAddGroup.isOpenMap_coe _
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)))

theorem sourceShell_subset_block :
    sourceShell ⊆ closedBall (0 : V1) 1 ×ˢ closedBall (0 : V2) 2 :=
  fun _ hx ↦ ⟨hx.1, mem_closedBall_zero_iff.mpr hx.2.2.le⟩

variable {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

def chartShell : TopologicalSpace.Opens V3 :=
  ⟨(e retained.index).target ∩ (e retained.index).symm ⁻¹' ambientShell L,
    (e retained.index).symm.continuousOn.isOpen_inter_preimage
      (e retained.index).open_target (ambientShell_isOpen L)⟩

theorem chartShell_subset_target :
    (chartShell L retained : Set V3) ⊆ (e retained.index).target := inter_subset_left

theorem chartShell_inverse_formula {x : V1 × V2} (hx : x ∈ sourceShell) :
    (e retained.index).symm (h x) = pi x := by
  rw [← retained.formula x (sourceShell_subset_block hx)]
  exact (e retained.index).left_inv (retained.contains x (sourceShell_subset_block hx))

theorem shell_subset_chartShell : shell h ⊆ (chartShell L retained : Set V3) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← retained.formula x (sourceShell_subset_block hx)]
    exact (e retained.index).mapsTo (retained.contains x (sourceShell_subset_block hx))
  · change (e retained.index).symm (h x) ∈ ambientShell L
    rw [chartShell_inverse_formula L retained hx]
    exact ⟨mem_univ _, x.2, hx.2, rfl⟩

theorem chartShell_nonempty : Nonempty (chartShell L retained) := by
  let x : source := ⟨(endpoint false, squareRimBase),
    sphere_subset_closedBall (endpoint_mem_sphere false), squareRimBase.property⟩
  exact ⟨⟨h (coordinates x), shell_subset_chartShell L retained
    ⟨coordinates x, coordinates_mem_sourceShell x.property, rfl⟩⟩⟩

def chartDomain : Set (chartShell L retained) :=
  {z | (e retained.index).symm (z : V3) ∈ R}

theorem chartDomain_image :
    (Subtype.val : chartShell L retained → V3) '' chartDomain L retained = shell h := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, hve⟩ := y.property.2.2
    let x : V1 × V2 := (((e retained.index).symm y).1, v)
    have hx : x ∈ sourceShell := ⟨hy.1, hv⟩
    have hproj : pi x = (e retained.index).symm y := Prod.ext rfl hve
    refine ⟨x, hx, ?_⟩
    rw [← retained.formula x (sourceShell_subset_block hx), hproj]
    exact (e retained.index).right_inv y.property.1
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨h x, shell_subset_chartShell L retained ⟨x, hx, rfl⟩⟩, ?_, rfl⟩
    change (e retained.index).symm (h x) ∈ R
    rw [chartShell_inverse_formula L retained hx]
    exact ⟨hx.1, mem_univ _⟩

theorem chartDomain_PL (he : PLDomain e R) :
    PLDomain (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
      (chartShell_nonempty L retained)) (chartDomain L retained) :=
  he.chart_image retained.index (chartShell L retained)
    (chartShell_nonempty L retained) (chartShell_subset_target L retained)

theorem chartDomain_frontier_iff
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    (z : chartShell L retained) (hz : (z : V3) ∈ shell h) :
    z ∈ frontier (chartDomain L retained) ↔
      h.symm (z : V3) ∈ frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) := by
  rw [show frontier (chartDomain L retained) =
      {y : chartShell L retained | (e retained.index).symm (y : V3) ∈ frontier R} from
    frontier_chart_image_eq (e retained.index) (chartShell L retained)
      (chartShell_nonempty L retained) (chartShell_subset_target L retained) R]
  obtain ⟨x, hx, hxy⟩ := hz
  change (e retained.index).symm (z : V3) ∈ frontier R ↔ _
  rw [← hxy, chartShell_inverse_formula L retained hx,
    h.left_inv (sourceShell_subset_source h hsource hx)]
  simp only [latticeHandleDomain, frontier_prod_univ_eq,
    frontier_closedBall _ one_ne_zero, mem_prod, mem_univ, and_true]
  rfl

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
