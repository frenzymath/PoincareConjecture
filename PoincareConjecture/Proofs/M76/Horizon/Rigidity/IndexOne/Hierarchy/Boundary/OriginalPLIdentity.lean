import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLPartition
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L

theorem standard_chartwisePLMap_identity
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) :
    ChartwisePLMap d d (latticeHandleMapInDomain (Fin 1) (Fin 2) L (ContinuousMap.id H)) := by
  classical
  have hid : latticeHandleMapInDomain (Fin 1) (Fin 2) L (ContinuousMap.id H) =
      ContinuousMap.id R := by
    apply ContinuousMap.ext
    intro x
    exact (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm_apply_apply x
  rw [hid]
  refine ⟨hd.domain, hd.domain, isOpen_univ, ?_⟩
  intro x _
  obtain ⟨i, hxi⟩ := hd.domain.cover x
  obtain ⟨a, ha⟩ := hd.inverse_formula i
  let ell : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 1)).toContinuousAffineMap.comp
      ((ContinuousLinearMap.fst ℝ V1 V2).toContinuousAffineMap.comp a.toContinuousAffineMap)
  have hmem (z : V3) (hz : z ∈ (d i).target) :
      (d i).symm z ∈ R ↔ -1 ≤ ell z ∧ ell z ≤ 1 := by
    rw [ha z hz]
    change (((a z).1 ∈ closedBall (0 : V1) 1) ∧ True) ↔ _
    rw [and_true, mem_closedBall_zero_iff]
    constructor
    · intro h
      exact abs_le.mp ((norm_le_pi_norm (a z).1 0).trans h)
    · intro h
      apply pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) |>.mpr
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact abs_le.mpr h
  obtain ⟨P, hP, hxP, hPt⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    (isCompact_singleton : IsCompact {d i x}) (d i).open_target
    (singleton_subset_iff.mpr ((d i).mapsTo hxi))
  let one : V3 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ V3 1
  obtain ⟨K, hK, hKs⟩ := P.exists_finite_triangulation_inter_halfspaces hP
    {(ell - one).toAffineMap, (-ell - one).toAffineMap}
  have hKspace : K.space = P.space ∩ {z | -1 ≤ ell z ∧ ell z ≤ 1} := by
    rw [hKs]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq]
    change (z ∈ P.space ∧ ell z - 1 ≤ 0 ∧ -ell z - 1 ≤ 0) ↔ _
    constructor <;> rintro ⟨hz, h1, h2⟩ <;> exact ⟨hz, by linarith, by linarith⟩
  have hKt : K.space ⊆ (d i).target := fun z hz => hPt ((hKspace.subset hz).1)
  have hKR : MapsTo (d i).symm K.space R := fun z hz =>
    (hmem z (hKt hz)).mpr (hKspace.subset hz).2
  let V : Set R := (fun y : R => (y : X)) ⁻¹'
    ((d i).source ∩ (d i) ⁻¹' interior P.space)
  have hV : IsOpen V :=
    ((d i).isOpen_inter_preimage isOpen_interior).preimage continuous_subtype_val
  refine ⟨i, i, K, V, id, hK, hV, ⟨hxi, hxP (mem_singleton _)⟩,
    subset_univ _, fun y hy => hy.1, ?_, hKt, ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    apply hKspace.symm.subset
    refine ⟨interior_subset hy.2, (hmem _ ((d i).mapsTo hy.1)).mp ?_⟩
    rw [(d i).left_inv hy.1]
    exact y.property
  · intro z hz
    exact ⟨⟨(d i).symm z, hKR hz⟩, mem_univ _, rfl⟩
  · exact (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK
  · intro y hy _
    exact ⟨hy, rfl⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
