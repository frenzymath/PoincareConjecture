import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.ClosedRegionBicollarSides
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.ChartwisePLBall

theorem bicollar_sides {E X ι : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S : Set X}
    (b : ChartwisePLBall e D S) (sph : ChartwisePLSphere e S)
    (A : Set E) (HB : A ≃ₜ S) (c : E × ℝ → X)
    {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn c (A ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (A ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hbase : ∀ z : A, c ((z : E), 0) = HB z)
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-r) r))) :
    (c '' (A ×ˢ Ioc 0 r) ⊆ interior D ∧ Disjoint (c '' (A ×ˢ Ico (-r) 0)) D) ∨
      (c '' (A ×ˢ Ico (-r) 0) ⊆ interior D ∧ Disjoint (c '' (A ×ˢ Ioc 0 r)) D) := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hproper (z : E × ℝ) (hz : z ∈ A ×ˢ Icc (-r) r) : c z ∈ S ↔ z.2 = 0 := by
    constructor
    · intro hzS
      let y := HB.symm ⟨c z, hzS⟩
      have hval : c ((y : E), 0) = c z := (hbase y).trans
        (congrArg Subtype.val (HB.apply_symm_apply ⟨c z, hzS⟩))
      have heq := hi.injective (a₁ := ⟨((y : E), 0), y.property, hzero⟩)
        (a₂ := ⟨z, hz⟩) hval
      exact (congrArg (fun w : (A ×ˢ Icc (-r) r : Set (E × ℝ)) => w.1.2) heq).symm
    · intro hz0
      have hzpair : z = (z.1, 0) := Prod.ext rfl hz0
      rw [hzpair, hbase ⟨z.1, hz.1⟩]
      exact (HB ⟨z.1, hz.1⟩).property
  have hA : IsConnected A := isConnected_iff_connectedSpace.mpr
    (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp sph.isConnected))
  have hpossub : A ×ˢ Ioc 0 r ⊆ A ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  have hnegsub : A ×ˢ Ico (-r) 0 ⊆ A ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  apply Poincare.Topology.opposite_sides_of_frontier_neighborhood b.isCompact.isClosed
    b.closure_interior (b.frontier_eq.symm ▸ sph.isConnected.nonempty) hopen
  · intro x hx
    rw [b.frontier_eq] at hx
    let y := HB.symm ⟨x, hx⟩
    refine ⟨((y : E), 0), ⟨y.property, by constructor <;> linarith⟩, ?_⟩
    exact (hbase y).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩))
  · rintro x ⟨z, hz, rfl⟩
    rcases lt_trichotomy z.2 0 with hneg | hzero | hpos
    · exact Or.inr ⟨z, ⟨hz.1, hz.2.1.le, hneg⟩, rfl⟩
    · apply Or.inl ∘ Or.inl
      rw [b.frontier_eq]
      exact (hproper z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩).mpr hzero
    · exact Or.inl (Or.inr ⟨z, ⟨hz.1, hpos, hz.2.2.le⟩, rfl⟩)
  · exact (hA.isPreconnected.prod isPreconnected_Ioc).image c (hc.mono hpossub)
  · exact (hA.isPreconnected.prod isPreconnected_Ico).image c (hc.mono hnegsub)
  · rw [b.frontier_eq]
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact hz.2.1.ne' ((hproper z (hpossub hz)).mp hx)
  · rw [b.frontier_eq]
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact hz.2.2.ne ((hproper z (hnegsub hz)).mp hx)

end PoincareConjecture.M76.ChartwisePLBall
