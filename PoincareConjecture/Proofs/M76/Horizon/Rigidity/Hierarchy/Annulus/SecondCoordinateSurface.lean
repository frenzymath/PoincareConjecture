import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.RegularSecondCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CompactMarkedImage

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

def HamiltonZeroSecondCoordinateRegularity {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (phi : C(H0, H0)) (theta : C0) : Prop :=
  let q : C(R, C0) := (hamiltonZeroSecondCircleMap phi).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  (∀ x : R, q x = theta →
    ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
      (T : OpenPartialHomeomorph X0 V3),
      (a : C0) = theta ∧ ell.contLinear v = 1 ∧
      (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
      ∀ y : R, (y : X0) ∈ T.source → (q y = theta ↔ ell (T y) = 0)) ∧
  ∀ x : R, (x : X0) ∈ frontier R → q x = theta →
    ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3)
      (T : OpenPartialHomeomorph X0 V3),
      (a : C0) = theta ∧ psi.contLinear u = 1 ∧
      ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
      (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
      (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
      (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
      ∀ y : R, (y : X0) ∈ T.source → (q y = theta ↔ ell (T y) = 0)

theorem exists_hamiltonZero_second_surface_polyhedral_charts {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ t ∈ Ioo (0 : ℝ) p,
      let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(t : C0)}
      IsCompact S ∧ HamiltonZeroSecondCoordinateRegularity e R phi (t : C0) ∧
      ∀ x ∈ S,
        ∃ (T : OpenPartialHomeomorph X0 V3) (V : Set X0)
          (cuts marks : Finset (V3 →ᵃ[ℝ] ℝ)),
          IsOpen V ∧ x ∈ V ∧ V ⊆ T.source ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ V, y ∈ S ↔ ∀ a ∈ cuts, a (T y) ≤ 0) ∧
          ∀ y ∈ V, y ∈ frontier R ↔ ∀ a ∈ marks, a (T y) ≤ 0 := by
  classical
  obtain ⟨t, ht, hcompact, hregular, hboundary⟩ :=
    exists_hamiltonZero_regular_second_coordinate e d hd phi hphi he
  refine ⟨t, ht, hcompact, ⟨hregular, hboundary⟩, ?_⟩
  intro x hxS
  let x' : R := ⟨x, hxS.1⟩
  have hxt : hamiltonZeroSecondCircleMap phi x = (t : C0) := hxS.2
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
        exact ⟨(hlevel ⟨y, hyS.1⟩ hy).mp hyS.2, (hTR y hy).mp hyS.1⟩
      · rintro ⟨hz, hp⟩
        have hyR := (hTR y hy).mpr hp
        exact ⟨hyR, (hlevel ⟨y, hyR⟩ hy).mpr hz⟩
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
      ⟨hxT, (mem_interior_iff_notMem_frontier hxS.1).mpr hxB⟩,
      inter_subset_left, hT, ?_, ?_⟩
    · intro y hy
      rw [hcuts]
      have hyR := interior_subset hy.2
      exact ⟨fun h => (hlevel ⟨y, hyR⟩ hy.1).mp h.2,
        fun h => ⟨hyR, (hlevel ⟨y, hyR⟩ hy.1).mpr h⟩⟩
    · intro y hy
      have hyB : y ∉ frontier R :=
        fun hb => disjoint_left.mp disjoint_interior_frontier hy.2 hb
      simp [marks, hyB]

end PoincareConjecture.M76
