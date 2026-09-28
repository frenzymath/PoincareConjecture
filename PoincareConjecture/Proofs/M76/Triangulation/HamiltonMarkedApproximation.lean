import PoincareConjecture.Proofs.M76.Triangulation.HamiltonTorusRigidity
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonRelativePLApproximation
import Mathlib.Analysis.Normed.Module.RCLike.Real










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))



theorem isCompact_latticeHandleDomain [DiscreteTopology L] [IsZLattice ℝ L] :
    IsCompact (latticeHandleDomain ι κ L) := by
  have hquot : IsCompact (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)) := by
    have h := IsZLattice.isCompact_range_of_periodic L
      (QuotientAddGroup.mk : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup))
      QuotientAddGroup.continuous_mk (by
        intro x z hz
        change QuotientAddGroup.mk' L.toAddSubgroup (x + z) =
          QuotientAddGroup.mk' L.toAddSubgroup x
        rw [map_add]
        have hz0 : (QuotientAddGroup.mk z : (κ → ℝ) ⧸ L.toAddSubgroup) = 0 :=
          (QuotientAddGroup.eq_zero_iff z).mpr hz
        change QuotientAddGroup.mk x + QuotientAddGroup.mk z = QuotientAddGroup.mk x
        rw [hz0, add_zero])
    rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at h
  exact (isCompact_closedBall (0 : ι → ℝ) 1).prod hquot

omit [Fintype κ] in



theorem latticeHandleDomainEquiv_preimage_boundary :
    (latticeHandleDomainEquiv ι κ L) ⁻¹' latticeHandleBoundary ι κ L =
      (Subtype.val : latticeHandleDomain ι κ L → LatticeHandleAmbient ι κ L) ⁻¹'
        frontier (latticeHandleDomain ι κ L) := by
  have hfront : frontier (latticeHandleDomain ι κ L) =
      sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)) := by
    rw [latticeHandleDomain, frontier_prod_univ_eq,
      frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  ext x
  rw [mem_preimage, mem_preimage, hfront]
  change (‖x.val.1‖ = 1 ∧ True) ↔ x.val.1 ∈ sphere (0 : ι → ℝ) 1 ∧ True
  simp only [mem_sphere, dist_zero_right]




theorem exists_hamilton_marked_relative_approximation
    [DiscreteTopology L] [IsZLattice ℝ L]
    {α β : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (approximation : HasRelativeBoundaryProperPLApproximation e d
      (latticeHandleDomain ι κ L))
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (U : Set (latticeHandleDomain ι κ L)) (hU : IsOpen U)
    (hBU : (Subtype.val : latticeHandleDomain ι κ L → LatticeHandleAmbient ι κ L) ⁻¹'
      frontier (latticeHandleDomain ι κ L) ⊆ U)
    (hidentity : ChartwisePLOn e d (ContinuousMap.id (latticeHandleDomain ι κ L)) U) :
    ∃ phi : C(LatticeHandle ι κ L, LatticeHandle ι κ L),
      ChartwisePLMap e d (latticeHandleMapInDomain ι κ L phi) ∧
      phi ⁻¹' latticeHandleBoundary ι κ L = latticeHandleBoundary ι κ L ∧
      Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel phi
        (latticeHandleBoundary ι κ L)) := by
  obtain ⟨phiR, hphiR, hproper, ⟨HR⟩⟩ := approximation
    (isCompact_latticeHandleDomain ι κ L) he hd.domain U hU hBU hidentity
  let q := latticeHandleDomainEquiv ι κ L
  let phi : C(LatticeHandle ι κ L, LatticeHandle ι κ L) :=
    ⟨fun x => q (phiR (q.symm x)), q.continuous.comp (phiR.continuous.comp q.symm.continuous)⟩
  have hphi : latticeHandleMapInDomain ι κ L phi = phiR := by
    apply ContinuousMap.ext
    intro x
    change q.symm (q (phiR (q.symm (q x)))) = phiR x
    rw [q.symm_apply_apply, q.symm_apply_apply]
  have hb (x : latticeHandleDomain ι κ L) :
      q x ∈ latticeHandleBoundary ι κ L ↔
        (x : LatticeHandleAmbient ι κ L) ∈ frontier (latticeHandleDomain ι κ L) :=
    Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary ι κ L) x
  have hbinv (x : LatticeHandle ι κ L) :
      (q.symm x : LatticeHandleAmbient ι κ L) ∈ frontier (latticeHandleDomain ι κ L) ↔
        x ∈ latticeHandleBoundary ι κ L := by
    simpa only [q.apply_symm_apply] using (hb (q.symm x)).symm
  refine ⟨phi, hphi ▸ hphiR, ?_, ?_⟩
  · ext x
    change q (phiR (q.symm x)) ∈ latticeHandleBoundary ι κ L ↔
      x ∈ latticeHandleBoundary ι κ L
    rw [hb]
    have h := Set.ext_iff.mp hproper (q.symm x)
    exact h.trans (hbinv x)
  · refine ⟨{
      toFun := fun z => q (HR (z.1, q.symm z.2))
      continuous_toFun := q.continuous.comp
        (HR.continuous.comp (continuous_fst.prodMk (q.symm.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_
    }⟩
    · intro x
      rw [HR.apply_zero]
      exact q.apply_symm_apply x
    · intro x
      rw [HR.apply_one]
      rfl
    · intro t x hx
      change q (HR (t, q.symm x)) = x
      rw [HR.eq_fst t ((hbinv x).mpr hx)]
      exact q.apply_symm_apply x

end PoincareConjecture.M76
