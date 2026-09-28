import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.FirstBoundaryCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledFrontierCovering
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.ComplementarySlabDomains



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem isCoveringMap_hamiltonZero_first_frontiers_of_installed_products
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hi : ∀ s, IsEmbedding (fun z : K s ×ˢ Icc (-rho) rho => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho → IsOpen (c s '' (K s ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, K s ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (b : C0) else (a : C0)} : Set X0))
    (hzero : ∀ s (x : K s), c s (x, 0) = (H s x : X0))
    (g : ∀ s, C(K s, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (hproduct : ∀ s (x : K s) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        (g s x, (if s then (b : C0) else (a : C0)) +
          (((if s then -1 else 1) * t : ℝ) : C0))) :
    ∀ side : Bool, IsCoveringMap (hamiltonZeroRetainedTangentialMap phi
      (frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
        (if side then b else a) (if side then a + p else b)))) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi) ha hab hb hfront
  have hfronts (side : Bool) : frontier (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)} := by
    cases side
    · exact hfront
    · simpa only [↓reduceIte, hcomp] using he.compl_interior.2.trans hfront
  obtain ⟨r, hr, _, hcollars⟩ := exists_hamiltonZero_first_boundary_collars
    phi F ha hab hb K hK hrho c hi hopen H hzero g hg hproduct hfronts
  intro side
  obtain ⟨collar, cover, hB, _, _, hiB, _, hzeroB, _, hcover, hvalue⟩ := hcollars side
  exact isCoveringMap_hamiltonZero_frontier_of_installed_collar phi hB hr.le
    collar hiB hzeroB cover hcover (fun x => hvalue x 0 ⟨by linarith, hr.le⟩)

end PoincareConjecture.M76
