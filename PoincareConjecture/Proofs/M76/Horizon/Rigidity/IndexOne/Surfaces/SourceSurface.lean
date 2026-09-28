import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.RegularSourcePhase
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CompactMarkedImage

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

def sourceSurface (phi : C(H, H)) (theta : C) : Set X :=
  Subtype.val '' {x : R | sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) = theta}

theorem sourceSurface_subset (phi : C(H, H)) (theta : C) :
    sourceSurface phi theta ⊆ R := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem mem_sourceSurface_iff (phi : C(H, H)) (theta : C) (x : R) :
    (x : X) ∈ sourceSurface phi theta ↔
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) = theta := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.ext heq : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem exists_sourceSurface_polyhedral_charts
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ t ∈ Ioo (0 : ℝ) p,
      IsCompact (sourceSurface phi (t : C)) ∧ (sourceSurface phi (t : C)).Nonempty ∧
      ∀ x ∈ sourceSurface phi (t : C),
        ∃ (T : OpenPartialHomeomorph X V3) (V : Set X)
          (cuts marks : Finset (V3 →ᵃ[ℝ] ℝ)),
          IsOpen V ∧ x ∈ V ∧ V ⊆ T.source ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ V, y ∈ sourceSurface phi (t : C) ↔ ∀ a ∈ cuts, a (T y) ≤ 0) ∧
          ∀ y ∈ V, y ∈ frontier R ↔ ∀ a ∈ marks, a (T y) ≤ 0 := by
  classical
  obtain ⟨t, ht, hcompact, hne, hregular, hboundary⟩ :=
    exists_sourcePhase_regular_level e d hd phi hphi F
  refine ⟨t, ht, hcompact.image continuous_subtype_val, hne.image _, ?_⟩
  intro x hxS
  have hxR := sourceSurface_subset phi (t : C) hxS
  let x' : R := ⟨x, hxR⟩
  have hxt := (mem_sourceSurface_iff phi (t : C) x').mp hxS
  by_cases hxB : x ∈ frontier R
  · obtain ⟨a, psi, ell, u, v, T, _, _, _, _, hxT, _, _, hT, hTR, hTB, _, hlevel⟩ :=
      hboundary x' hxB hxt
    let A := ell.toAffineMap
    let P := psi.toAffineMap
    let cuts : Finset (V3 →ᵃ[ℝ] ℝ) := {A, -A, -P}
    let marks : Finset (V3 →ᵃ[ℝ] ℝ) := {P, -P}
    have hcuts (z : V3) : (∀ a ∈ cuts, a z ≤ 0) ↔ ell z = 0 ∧ 0 ≤ psi z := by
      simp only [cuts, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (ell z ≤ 0 ∧ -ell z ≤ 0 ∧ -psi z ≤ 0) ↔ _
      simp only [neg_nonpos]
      exact ⟨fun h => ⟨le_antisymm h.1 h.2.1, h.2.2⟩, fun h => ⟨h.1.le, h.1.ge, h.2⟩⟩
    have hmarks (z : V3) : (∀ a ∈ marks, a z ≤ 0) ↔ psi z = 0 := by
      simp only [marks, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (psi z ≤ 0 ∧ -psi z ≤ 0) ↔ _
      rw [neg_nonpos]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
    refine ⟨T, T.source, cuts, marks, T.open_source, hxT, Subset.rfl, hT, ?_, ?_⟩
    · intro y hy
      rw [hcuts]
      constructor
      · intro hyS
        have hyR := sourceSurface_subset phi (t : C) hyS
        exact ⟨(hlevel ⟨y, hyR⟩ hy).mp
          ((mem_sourceSurface_iff phi (t : C) ⟨y, hyR⟩).mp hyS), (hTR y hy).mp hyR⟩
      · rintro ⟨hz, hp⟩
        have hyR := (hTR y hy).mpr hp
        exact (mem_sourceSurface_iff phi (t : C) ⟨y, hyR⟩).mpr
          ((hlevel ⟨y, hyR⟩ hy).mpr hz)
    · exact fun y hy => (hTB y hy).trans (hmarks (T y)).symm
  · obtain ⟨a, ell, v, T, _, _, hxT, _, hT, _, hlevel⟩ := hregular x' hxt
    let V := T.source ∩ interior R
    let A := ell.toAffineMap
    let cuts : Finset (V3 →ᵃ[ℝ] ℝ) := {A, -A}
    let marks : Finset (V3 →ᵃ[ℝ] ℝ) := {AffineMap.const ℝ V3 (1 : ℝ)}
    have hcuts (z : V3) : (∀ a ∈ cuts, a z ≤ 0) ↔ ell z = 0 := by
      simp only [cuts, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (ell z ≤ 0 ∧ -ell z ≤ 0) ↔ _
      rw [neg_nonpos]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
    refine ⟨T, V, cuts, marks, T.open_source.inter isOpen_interior,
      ⟨hxT, (mem_interior_iff_notMem_frontier hxR).mpr hxB⟩,
      inter_subset_left, hT, ?_, ?_⟩
    · intro y hy
      rw [hcuts]
      exact (mem_sourceSurface_iff phi (t : C) ⟨y, interior_subset hy.2⟩).trans
        (hlevel ⟨y, interior_subset hy.2⟩ hy.1)
    · intro y hy
      have hyB : y ∉ frontier R :=
        fun hb => disjoint_left.mp disjoint_interior_frontier hy.2 hb
      simp [marks, hyB]

end PoincareConjecture.M76.HamiltonIntervalTorus
