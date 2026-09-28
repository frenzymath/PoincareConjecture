import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.FirstBoundaryCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceBoundaryAlternative
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

theorem exists_hamiltonZero_first_slab_disk_alternatives
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {alpha beta : ℝ} (ha : 0 < alpha) (hab : alpha < beta) (hb : beta < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta) =
      hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hI : ∀ side : Bool, IsPLIrreducible e (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)))
    (hinj : ∀ side : Bool, ∀ x : (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x))
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hi : ∀ s, IsEmbedding (fun z : (K s ×ˢ Icc (-rho) rho : Set (E × ℝ)) => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho → IsOpen (c s '' (K s ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, K s ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} : Set X0))
    (hzero : ∀ s (x : K s), c s (x, 0) = H s x)
    (g : ∀ s, C(K s, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (hproduct : ∀ s (x : K s) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        (g s x, (if s then (beta : C0) else (alpha : C0)) +
          (((if s then -1 else 1) * t : ℝ) : C0))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧ ∀ side : Bool,
      let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
        (if side then beta else alpha) (if side then alpha + p else beta)
      let B := Sum.inl '' K false ∪ Sum.inr '' K true
      ∃ (collar : (E ⊕ E) × ℝ → X0) (cover : C(B, C0 × C0)),
        IsCompact B ∧ B.Nonempty ∧ ContinuousOn collar (B ×ˢ Icc (-r) r) ∧
        IsEmbedding (fun z : (B ×ˢ Icc (-r) r : Set ((E ⊕ E) × ℝ)) => collar z) ∧
        IsOpen (collar '' (B ×ˢ Ioo (-r) r)) ∧
        collar '' (B ×ˢ ({0} : Set ℝ)) = frontier R ∧
        (∀ z ∈ B ×ˢ Icc (-r) r, collar z ∈ R ↔ 0 ≤ z.2) ∧
        IsCoveringMap cover ∧
        (∀ x : B, ∀ t ∈ Icc (-r) r,
          (Q0 (hamiltonZeroAmbientMap phi (collar (x, t)))).1 = cover x) ∧
        (HamiltonZeroSourceBoundaryDiskData e d phi R
          (if side then beta else alpha) (if side then alpha + p else beta) ∨
          HamiltonZeroBoundaryFailureArc e R phi) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : Zero (E ⊕ E) := ⟨Sum.inl 0⟩
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi) ha hab hb hfront
  have hfronts (side : Bool) : frontier (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)) =
        hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)} := by
    cases side
    · exact hfront
    · change frontier (hamiltonZeroCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p beta (alpha + p)) = _
      rw [← hcomp, he.frontier_closed_exterior]
      exact hfront
  obtain ⟨r, hr, hrrho, collars⟩ := exists_hamiltonZero_first_boundary_collars
    phi F ha hab hb K hK hrho c hi hopen H hzero g hg hproduct hfronts
  refine ⟨r, hr, hrrho, ?_⟩
  intro side R B
  obtain ⟨collar, cover, hB, hBne, hc, hci, hco, hczero, hcside, hcover, hcproduct⟩ := collars side
  refine ⟨collar, cover, hB, hBne, hc, hci, hco, hczero, hcside, hcover, hcproduct, ?_⟩
  have hmark : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹'
      {((if side then beta else alpha : ℝ) : C0), ((if side then alpha + p else beta : ℝ) : C0)} := by
    rw [hfronts side]
    cases side
    · exact Subset.rfl
    · simp only [if_true, AddCircle.coe_add_period, pair_comm]
      exact Subset.rfl
  have hcut : ∃ cut : ℝ, cut < (if side then beta else alpha) ∧
      (if side then beta else alpha) < (if side then alpha + p else beta) ∧
      (if side then alpha + p else beta) < cut + p := by
    cases side
    · exact ⟨0, ha, hab, by simpa using hb⟩
    · refine ⟨(alpha + beta) / 2, ?_, ?_, ?_⟩ <;> dsimp <;> linarith
  obtain ⟨cut, hcut, horder, hwidth⟩ := hcut
  exact exists_hamiltonZero_source_boundary_disk_alternative e d hd phi hphi F (hI side)
    hcut horder hwidth Subset.rfl hmark (hinj side) hB hBne hr collar hc hci hco hczero
    hcside cover hcover hcproduct

end PoincareConjecture.M76
