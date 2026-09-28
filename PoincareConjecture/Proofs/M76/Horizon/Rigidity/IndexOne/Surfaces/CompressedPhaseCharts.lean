import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.MarkedRimCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem exists_compressed_sourceSurface_polyhedral_charts
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) {a b : ℝ} {theta theta' : C}
    (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧ lambda.contLinear v = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi a b ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi a b ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∀ x ∈ sourceSurface phi theta,
      ∃ (T : OpenPartialHomeomorph X V3) (V : Set X)
        (cuts marks : Finset (V3 →ᵃ[ℝ] ℝ)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ T.source ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ V, y ∈ sourceSurface phi theta ↔ ∀ c ∈ cuts, c (T y) ≤ 0) ∧
        ∀ y ∈ V, y ∈ sourceSurface phi theta ∩ frontier R ↔
          ∀ c ∈ marks, c (T y) ≤ 0 := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hSF : sourceSurface phi theta ⊆ frontier (sourceSlab phi a b) :=
    fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx))
  have hSN := hSF.trans he.closed.frontier_subset
  intro x hxS
  by_cases hxR : x ∈ frontier R
  · obtain ⟨psi, lambda, w, v, T, _, _, _, hxT, _, hT, _, hold, hphase⟩ :=
      hcorner x ⟨hxS, hxR⟩
    let P := psi.toAffineMap
    let A := lambda.toAffineMap
    let cuts : Finset (V3 →ᵃ[ℝ] ℝ) := {P, -P, A}
    let marks : Finset (V3 →ᵃ[ℝ] ℝ) := {P, -P, A, -A}
    have hcuts (z : V3) : (∀ c ∈ cuts, c z ≤ 0) ↔
        psi z = 0 ∧ lambda z ≤ 0 := by
      simp only [cuts, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (psi z ≤ 0 ∧ -psi z ≤ 0 ∧ lambda z ≤ 0) ↔ _
      rw [neg_nonpos]
      exact ⟨fun h => ⟨le_antisymm h.1 h.2.1, h.2.2⟩,
        fun h => ⟨h.1.le, h.1.ge, h.2⟩⟩
    have hmarks (z : V3) : (∀ c ∈ marks, c z ≤ 0) ↔
        psi z = 0 ∧ lambda z = 0 := by
      simp only [marks, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (psi z ≤ 0 ∧ -psi z ≤ 0 ∧ lambda z ≤ 0 ∧ -lambda z ≤ 0) ↔ _
      simp only [neg_nonpos]
      exact ⟨fun h => ⟨le_antisymm h.1 h.2.1, le_antisymm h.2.2.1 h.2.2.2⟩,
        fun h => ⟨h.1.le, h.1.ge, h.2.le, h.2.ge⟩⟩
    refine ⟨T, T.source, cuts, marks, T.open_source, hxT, Subset.rfl, hT, ?_, ?_⟩
    · intro y hy
      exact (hphase y hy).trans (hcuts (T y)).symm
    · intro y hy
      rw [hmarks]
      constructor
      · intro hyS
        have hp := (hphase y hy).mp hyS.1
        have ho := (hold y hy).mp ⟨hSN hyS.1, hyS.2⟩
        exact ⟨hp.1, le_antisymm hp.2 ho.2⟩
      · intro h
        exact ⟨(hphase y hy).mpr ⟨h.1, h.2.le⟩,
          ((hold y hy).mpr ⟨h.1, h.2.ge⟩).2⟩
  · obtain ⟨ell, v, T, hv, hxT, _, hT, hhalf⟩ := he.halfspace x (hSF hxS)
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hv'
      norm_num at hv'
    have himage := T.isImage_frontier_of_affine_nonneg ell hell hhalf
    let V := (T.source ∩ (frontier R)ᶜ) ∩ (sourceSurface phi theta')ᶜ
    let A := ell.toAffineMap
    let cuts : Finset (V3 →ᵃ[ℝ] ℝ) := {A, -A}
    let marks : Finset (V3 →ᵃ[ℝ] ℝ) := {AffineMap.const ℝ V3 (1 : ℝ)}
    have hcuts (z : V3) : (∀ c ∈ cuts, c z ≤ 0) ↔ ell z = 0 := by
      simp only [cuts, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      change (ell z ≤ 0 ∧ -ell z ≤ 0) ↔ _
      rw [neg_nonpos]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
    have hxOther : x ∉ sourceSurface phi theta' :=
      fun h => Set.disjoint_left.mp hAB hxS h
    refine ⟨T, V, cuts, marks,
      (T.open_source.inter isClosed_frontier.isOpen_compl).inter
        (sourceSurface_isCompact phi theta').isClosed.isOpen_compl,
      ⟨⟨hxT, hxR⟩, hxOther⟩, fun _ h => h.1.1, hT, ?_, ?_⟩
    · intro y hy
      rw [hcuts]
      have hlocal : y ∈ sourceSurface phi theta ↔ y ∈ frontier (sourceSlab phi a b) := by
        refine ⟨fun h => hSF h, ?_⟩
        intro h
        rcases hfront.subset h with h | h
        · exact False.elim (hy.1.2 h.2)
        · exact h.resolve_right hy.2
      exact hlocal.trans (himage.apply_mem_iff hy.1.1).symm
    · intro y hy
      have hnot : y ∉ sourceSurface phi theta ∩ frontier R := fun h => hy.1.2 h.2
      simp [marks, hnot]

end PoincareConjecture.M76.HamiltonIntervalTorus
