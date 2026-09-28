import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.CompressedPhaseCharts
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem exists_compressed_sourceSurface_plane_halfplane_charts
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
    ∀ x ∈ sourceSurface phi theta, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ sourceSurface phi theta ↔ ell (T y) = 0) ∧
          Disjoint T.source (frontier R)) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ sourceSurface phi theta ↔
            ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ sourceSurface phi theta →
            (y ∈ frontier R ↔ psi (T y) = 0)) := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hSF : sourceSurface phi theta ⊆ frontier (sourceSlab phi a b) :=
    fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx))
  have hSN := hSF.trans he.closed.frontier_subset
  intro x hxS
  by_cases hxR : x ∈ frontier R
  · obtain ⟨ell, lambda, w, z, T, hw, hz, hlz, hxT, _, hT, _, hold, hphase⟩ :=
      hcorner x ⟨hxS, hxR⟩
    refine ⟨T, hxT, hT, Or.inr ⟨ell, -lambda, -z,
      w - lambda.contLinear w • z, ?_, ?_, ?_, ?_, ?_⟩⟩
    · change -lambda.contLinear (-z) = 1
      rw [map_neg, neg_neg, hlz]
    · simp [map_sub, map_smul, hw, hz]
    · simp [map_sub, map_smul, hlz]
    · intro y hy
      simpa only [ContinuousAffineMap.neg_apply, neg_nonneg] using hphase y hy
    · intro y hy hyS
      have hp := (hphase y hy).mp hyS
      change y ∈ frontier R ↔ -lambda (T y) = 0
      rw [neg_eq_zero]
      constructor
      · intro hyR
        exact le_antisymm hp.2 ((hold y hy).mp ⟨hSN hyS, hyR⟩).2
      · intro hy0
        exact ((hold y hy).mpr ⟨hp.1, hy0.ge⟩).2
  · obtain ⟨ell, v, T, hv, hxT, _, hT, hhalf⟩ := he.halfspace x (hSF hxS)
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hv'
      norm_num at hv'
    have himage := T.isImage_frontier_of_affine_nonneg ell hell hhalf
    let W := (frontier R)ᶜ ∩ (sourceSurface phi theta')ᶜ
    have hW : IsOpen W := isClosed_frontier.isOpen_compl.inter
      (sourceSurface_isCompact phi theta').isClosed.isOpen_compl
    let T' := T.restrOpen W hW
    have hxW : x ∈ W := ⟨hxR, fun h => disjoint_left.mp hAB hxS h⟩
    refine ⟨T', ⟨hxT, hxW⟩, ?_, Or.inl ⟨ell, v, hv, ?_, ?_⟩⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right T (hT i) hW
    · intro y hy
      have hlocal : y ∈ sourceSurface phi theta ↔ y ∈ frontier (sourceSlab phi a b) := by
        refine ⟨fun h => hSF h, ?_⟩
        intro h
        rcases hfront.subset h with h | h
        · exact False.elim (hy.2.1 h.2)
        · exact h.resolve_right hy.2.2
      exact hlocal.trans (himage.apply_mem_iff hy.1).symm
    · exact disjoint_left.mpr (fun y hy hyR => hy.2.1 hyR)

end PoincareConjecture.M76.HamiltonIntervalTorus
