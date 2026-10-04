import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLatticeHandleModel
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLHomeomorph

/-!
# Protected Dehn surfaces and irreducible replacement

These are statement-only geometric inputs. They retain the fixed
lattice, original chart, full parametrized attaching curves, enclosing
side and actual atlas agreement. No existence theorem or reduction
to handle straightening is asserted. See Hamilton 1976, pp. 66--67
and M76 derivations 320, 331 and 337.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

section Markings

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

/-- The literal product-coordinate projection for the one fixed lattice.
See Hamilton pp. 66--67 and derivation337. -/
def hamiltonMarkedProjection (x : (ι → ℝ) × (κ → ℝ)) :
    LatticeHandleAmbient ι κ L := (x.1, QuotientAddGroup.mk x.2)

/-- The marked compact block C_r in the original handle torus.
See Hamilton pp. 66--67 and derivation337. -/
def hamiltonHandleBlock (r : ℝ) : Set (LatticeHandleAmbient ι κ L) :=
  hamiltonMarkedProjection ι κ L ''
    (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) r)

/-- The complete marked attaching patch A_r on the old boundary.
See Hamilton p. 67 and derivation337. -/
def hamiltonAttachingBlock (r : ℝ) : Set (LatticeHandleAmbient ι κ L) :=
  hamiltonMarkedProjection ι κ L ''
    (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) r)

variable {α : Type*}

/-- One original chart retained on the whole embedded C_2, with its
literal quotient and coordinate formula. See derivation337. -/
structure HamiltonRetainedBlockChart
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (h : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) V3) where
  quotient_injective : InjOn (hamiltonMarkedProjection ι κ L)
    (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2)
  index : α
  contains : ∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
    hamiltonMarkedProjection ι κ L x ∈ (e index).source
  formula : ∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
    e index (hamiltonMarkedProjection ι κ L x) = h x

/-- The enclosing side and complete PL sphere obtained by joining the
same Dehn surfaces to the fixed old-boundary patch. This does not assume
that its region is already a PL ball. See derivation337. -/
structure HamiltonDehnEnclosingRegion
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (T : Set (LatticeHandleAmbient ι κ L)) where
  region : Set (LatticeHandleAmbient ι κ L)
  compact : IsCompact region
  core_subset : hamiltonHandleBlock ι κ L 1 ⊆ region
  subset_outer : region ⊆ hamiltonHandleBlock ι κ L 2
  subset_outer_open : region ⊆ hamiltonMarkedProjection ι κ L ''
    (closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) 2)
  core_relative_interior :
    (Subtype.val : latticeHandleDomain ι κ L → LatticeHandleAmbient ι κ L) ⁻¹'
      hamiltonHandleBlock ι κ L 1 ⊆
        interior ((Subtype.val : latticeHandleDomain ι κ L →
          LatticeHandleAmbient ι κ L) ⁻¹' region)
  frontier_eq : frontier region = T ∪ hamiltonAttachingBlock ι κ L (3 / 2)
  old_boundary_eq : region ∩ frontier (latticeHandleDomain ι κ L) =
    hamiltonAttachingBlock ι κ L (3 / 2)
  sphere : ChartwisePLSphere e (frontier region)

end Markings

section Dehn

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

/-- The index-one annulus, including the values of both whole boundary
circles and its exact incidence with the whole old boundary.
See Hamilton p. 67 and derivation337. -/
structure HamiltonProtectedDehnAnnulus
    (L : Submodule ℤ V2) {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3) where
  surface : Set (LatticeHandleAmbient (Fin 1) (Fin 2) L)
  parametrization : (closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1) ≃ₜ surface
  map : V1 × V2 → LatticeHandleAmbient (Fin 1) (Fin 2) L
  map_eq : ∀ x : closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1,
    map x = (parametrization x : LatticeHandleAmbient (Fin 1) (Fin 2) L)
  piecewiseAffine : PolyhedralPLInCharts e map
    (closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1)
  inside : surface ⊆ hamiltonHandleBlock (Fin 1) (Fin 2) L 2 \
    hamiltonHandleBlock (Fin 1) (Fin 2) L 1
  inside_outer_open : surface ⊆ hamiltonMarkedProjection (Fin 1) (Fin 2) L ''
    (closedBall (0 : V1) 1 ×ˢ ball (0 : V2) 2)
  boundary_values : ∀ x ∈ sphere (0 : V1) 1 ×ˢ sphere (0 : V2) 1,
    map x = (x.1, QuotientAddGroup.mk ((3 / 2 : ℝ) • x.2))
  old_boundary_iff : ∀ x : closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1,
    (parametrization x : LatticeHandleAmbient (Fin 1) (Fin 2) L) ∈
        frontier (latticeHandleDomain (Fin 1) (Fin 2) L) ↔
      (x : V1 × V2).1 ∈ sphere (0 : V1) 1

/-- The index-two pair of simultaneously disjoint disks, with the
negative and positive radius-3/2 boundary values fixed pointwise.
See Hamilton p. 67 and derivation337. -/
structure HamiltonProtectedDehnDisks
    (L : Submodule ℤ V1) {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3) where
  surface : Bool → Set (LatticeHandleAmbient (Fin 2) (Fin 1) L)
  parametrization : ∀ b, closedBall (0 : V2) 1 ≃ₜ surface b
  map : Bool → V2 → LatticeHandleAmbient (Fin 2) (Fin 1) L
  map_eq : ∀ b (x : closedBall (0 : V2) 1),
    map b x = (parametrization b x : LatticeHandleAmbient (Fin 2) (Fin 1) L)
  piecewiseAffine : ∀ b, PolyhedralPLInCharts e (map b) (closedBall (0 : V2) 1)
  inside : ∀ b, surface b ⊆ hamiltonHandleBlock (Fin 2) (Fin 1) L 2 \
    hamiltonHandleBlock (Fin 2) (Fin 1) L 1
  inside_outer_open : ∀ b, surface b ⊆ hamiltonMarkedProjection (Fin 2) (Fin 1) L ''
    (closedBall (0 : V2) 1 ×ˢ ball (0 : V1) 2)
  disjoint : Disjoint (surface false) (surface true)
  boundary_values : ∀ b x, x ∈ sphere (0 : V2) 1 →
    map b x = (x, QuotientAddGroup.mk (fun _ : Fin 1 =>
      if b then (3 / 2 : ℝ) else -(3 / 2 : ℝ)))
  old_boundary_iff : ∀ b (x : closedBall (0 : V2) 1),
    (parametrization b x : LatticeHandleAmbient (Fin 2) (Fin 1) L) ∈
        frontier (latticeHandleDomain (Fin 2) (Fin 1) L) ↔
      (x : V2) ∈ sphere (0 : V2) 1

/-- The index-one protected Dehn assertion for a supplied original
chart and its retained atlas. The enclosing-side conclusion is an
explicit part of this geometric input. See derivation337. -/
def HasHamiltonProtectedDehnAnnulus
    (L : Submodule ℤ V2) {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3) : Prop :=
  PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L) →
    ∀ h : OpenPartialHomeomorph (V1 × V2) V3,
      closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source →
        ∀ N : Set (V1 × V2), IsOpen N →
          frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N →
            LocallyPiecewiseAffineOn h (h.source ∩ N) →
              Nonempty (HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) →
                ∃ T : HamiltonProtectedDehnAnnulus L e,
                  Nonempty (HamiltonDehnEnclosingRegion (Fin 1) (Fin 2) L e T.surface)

/-- The index-two protected Dehn assertion returns the same disjoint
pair in its enclosing sphere, rather than two independently selected
disks. See Hamilton p. 67 and derivation337. -/
def HasHamiltonProtectedDehnDisks
    (L : Submodule ℤ V1) {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3) : Prop :=
  PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L) →
    ∀ h : OpenPartialHomeomorph (V2 × V1) V3,
      closedBall (0 : V2) 1 ×ˢ (univ : Set V1) ⊆ h.source →
        ∀ N : Set (V2 × V1), IsOpen N →
          frontier (closedBall (0 : V2) 1 ×ˢ (univ : Set V1)) ⊆ N →
            LocallyPiecewiseAffineOn h (h.source ∩ N) →
              Nonempty (HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) →
                ∃ T : HamiltonProtectedDehnDisks L e,
                  Nonempty (HamiltonDehnEnclosingRegion (Fin 2) (Fin 1) L e
                    (⋃ b, T.surface b))

/-- Both concrete protected Dehn cases, with the actual lattice and
atlas quantified. This defines the missing geometric assertion; it
does not prove the generalized Dehn theorem or its side adapter.
See Hamilton p. 67 and derivation337. -/
def HasHamiltonProtectedDehnSurfaces : Prop :=
  (∀ (L : Submodule ℤ V2) [DiscreteTopology L], IsZLattice ℝ L →
    ∀ (α : Type) (e : α →
      OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3),
      HasHamiltonProtectedDehnAnnulus L e) ∧
  (∀ (L : Submodule ℤ V1) [DiscreteTopology L], IsZLattice ℝ L →
    ∀ (α : Type) (e : α →
      OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3),
      HasHamiltonProtectedDehnDisks L e)

/-- The separate proper-disk use of the generalized Dehn theorem in a
standard PL complementary domain. The supplied continuous filling is
the actual nullhomotopy, and the entire original boundary parametrization
is preserved. Properness keeps the disk interior off the whole domain
boundary. This is an input, not a disk-existence theorem. See Hamilton
p. 67 and M76 derivations337/338. -/
def HasHamiltonStandardProperDehnDisks : Prop :=
  ∀ R : Set V3, IsCompact R →
    PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R →
      ∀ S : Set V3, S ⊆ frontier R →
        ∀ gamma : sphere (0 : V2) 1 ≃ₜ S, gamma.IsFinitePL →
          ∀ F : C(closedBall (0 : V2) 1, R),
            (∀ x : sphere (0 : V2) 1,
              (F ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) →
            ∃ (D : Set V3) (b : closedBall (0 : V2) 1 ≃ₜ D),
              IsCompact D ∧ D ⊆ R ∧ b.IsFinitePL ∧
              (∀ x : sphere (0 : V2) 1,
                (b ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) ∧
              ∀ x : closedBall (0 : V2) 1,
                (b x : V3) ∈ frontier R ↔ (x : V2) ∈ sphere (0 : V2) 1

/-- The first protected-surface construction and the second complementary
proper-disk application are distinct clauses of the same generalized-Dehn
input node. Neither clause assumes the eventual core-placement map.
See Hamilton p. 67 and M76 derivations337/338. -/
def HasHamiltonGeneralizedDehnInput : Prop :=
  HasHamiltonProtectedDehnSurfaces ∧ HasHamiltonStandardProperDehnDisks

end Dehn

section Prime

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) {α : Type*}

/-- The actual protected PL ball for prime replacement. In index zero
it may be an arbitrary interior chart ball. In indices one and two
it retains the whole larger Dehn region and its marked attaching patch.
See Hamilton p. 67 and derivations331/337. -/
structure HamiltonMarkedProtectedBall
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (D : Set (LatticeHandleAmbient ι κ L)) where
  ball : ChartwisePLBall e D (frontier D)
  subset_domain : D ⊆ latticeHandleDomain ι κ L
  position :
    (Fintype.card ι = 0 ∧ D ⊆ interior (latticeHandleDomain ι κ L)) ∨
    ((Fintype.card ι = 1 ∨ Fintype.card ι = 2) ∧
      hamiltonHandleBlock ι κ L 1 ⊆ D ∧ D ⊆ hamiltonHandleBlock ι κ L 2 ∧
      D ⊆ hamiltonMarkedProjection ι κ L ''
        (closedBall (0 : ι → ℝ) 1 ×ˢ Metric.ball (0 : κ → ℝ) 2) ∧
      (Subtype.val : latticeHandleDomain ι κ L → LatticeHandleAmbient ι κ L) ⁻¹'
        hamiltonHandleBlock ι κ L 1 ⊆
          interior ((Subtype.val : latticeHandleDomain ι κ L →
            LatticeHandleAmbient ι κ L) ⁻¹' D) ∧
      D ∩ frontier (latticeHandleDomain ι κ L) = hamiltonAttachingBlock ι κ L (3 / 2))

/-- Protected irreducible replacement on the same marked lattice
handle. Its actual replacement atlas agrees in both identity-map
directions near the protected ball and whole old boundary. The source
cone/decomposition construction remains an obligation to prove this
predicate, rather than an unnamed output hidden in it. See Hamilton
p. 67 and derivation337. -/
def HasHamiltonProtectedIrreducibleReplacement
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3) : Prop :=
  Fintype.card ι + Fintype.card κ = 3 → Fintype.card ι ≤ 2 →
    ∀ [DiscreteTopology L], IsZLattice ℝ L →
      PLDomain e (latticeHandleDomain ι κ L) →
        ∀ D : Set (LatticeHandleAmbient ι κ L),
          Nonempty (HamiltonMarkedProtectedBall ι κ L e D) →
            ∃ (charts : Set (OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
              (N : Set (LatticeHandleAmbient ι κ L)),
              IsOpen N ∧ D ∪ frontier (latticeHandleDomain ι κ L) ⊆ N ∧
              IsPLIrreducible (fun c : charts => (c :
                OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
                (latticeHandleDomain ι κ L) ∧
              ChartwisePLOn e (fun c : charts => (c :
                OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
                (ContinuousMap.id (latticeHandleDomain ι κ L))
                ((Subtype.val : latticeHandleDomain ι κ L →
                  LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
              ChartwisePLOn (fun c : charts => (c :
                OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)) e
                (ContinuousMap.id (latticeHandleDomain ι κ L))
                ((Subtype.val : latticeHandleDomain ι κ L →
                  LatticeHandleAmbient ι κ L) ⁻¹' N)

end Prime

end PoincareMT.M76
