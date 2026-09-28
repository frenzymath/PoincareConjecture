import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Disks.RetainedSlabs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.ChartProperDisk










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1




theorem exists_protected_disk_pair
    (L : Submodule ℤ V1) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3)
    (he : PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L))
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)
    {N : Set (V2 × V1)} (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    ∃ T : HamiltonProtectedDehnDisks L e,
      (∀ b, IsCompact (T.surface b)) ∧ ∀ b, T.surface b ⊆ ambientSlab L b := by
  classical
  have hex (b : Bool) := exists_proper_disk_in_chart he retained.index
    (chartSlab L retained b) (chartSlab_nonempty L retained b)
    (chartSlab_subset_target L retained b) (rim h hsource b)
    (rim_finitePL h hsource hboundary hPL b) (chartFilling L retained hsource b)
    (chartFilling_rim L retained hsource b) (rim_inverse_frontier L retained hsource b)
  choose D p j hcompact hsub hj hmap hrim hproper using hex
  have hslab (b : Bool) : D b ⊆ ambientSlab L b := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := (hsub b hy).2
    exact hzy ▸ hz.2
  have hprotected (b : Bool) (y : LatticeHandleAmbient (Fin 2) (Fin 1) L) (hy : y ∈ D b) :
      y ∈ hamiltonHandleBlock (Fin 2) (Fin 1) L 2 \
          hamiltonHandleBlock (Fin 2) (Fin 1) L 1 ∧
        y ∈ hamiltonMarkedProjection (Fin 2) (Fin 1) L '' (D2 ×ˢ ball (0 : V1) 2) := by
    obtain ⟨z, hz, hzy⟩ := (hsub b hy).2
    have hzR : (e retained.index).symm z ∈ latticeHandleDomain (Fin 2) (Fin 1) L :=
      hzy.symm ▸ (hsub b hy).1
    exact hzy ▸ inverse_chartDomain_protected L retained b ⟨⟨z, hz⟩, hzR⟩
  refine ⟨{
    surface := D
    parametrization := p
    map := j
    map_eq := hmap
    piecewiseAffine := hj
    inside := fun b y hy => (hprotected b y hy).1
    inside_outer_open := fun b y hy => (hprotected b y hy).2
    disjoint := (ambientSlab_disjoint L retained).mono (hslab false) (hslab true)
    boundary_values := ?_
    old_boundary_iff := hproper
  }, hcompact, hslab⟩
  intro b x hx
  rw [hmap b ⟨x, sphere_subset_closedBall hx⟩, hrim b ⟨x, hx⟩]
  exact chartSlab_inverse_formula L retained ⟨sphere_subset_closedBall hx, height_mem_transverse b⟩



theorem nonempty_protected_disks
    (L : Submodule ℤ V1) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3)
    (he : PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L))
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)
    {N : Set (V2 × V1)} (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    Nonempty (HamiltonProtectedDehnDisks L e) := by
  obtain ⟨T, _, _⟩ := exists_protected_disk_pair L e he h hsource hboundary hPL retained
  exact ⟨T⟩

end PoincareConjecture.M76.Dehn.ProtectedDisks
