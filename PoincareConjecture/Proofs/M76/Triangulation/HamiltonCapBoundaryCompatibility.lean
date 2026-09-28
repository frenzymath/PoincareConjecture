import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapTransitionFormulas
import PoincareConjecture.Proofs.M76.Mathlib.LocalPLCollarTransition
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonMarkedCapCoordinates

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {D S : Set X} {eps : ℝ} {g : S × Ico (0 : ℝ) eps → X}

local notation "M" => (ℝ × E)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem original_frontier (B : OpenPartialHomeomorph X M)
    (hB : ∀ x ∈ B.source, x ∈ D ↔ (B x).1 ≤ 0) (x : X) (hx : x ∈ B.source) :
    x ∈ frontier D ↔ (B x).1 = 0 := by
  have hi : B.IsImage D {p | p.1 ≤ 0} := fun {y} hy => (hB y hy).symm
  have heq : frontier {p : M | p.1 ≤ 0} = {p | p.1 = 0} := by
    change frontier ((Prod.fst : M → ℝ) ⁻¹' Iic 0) = (Prod.fst : M → ℝ) ⁻¹' {0}
    rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst, frontier_Iic]
  have h := hi.frontier.apply_mem_iff hx
  rw [heq] at h
  exact h.symm





theorem compatible (c d : HamiltonMarkedCapCoordinates (E := E) (D := D) g)
    (hg : ∀ p, g p ∈ D) (hinj : Function.Injective g)
    (hcompat : c.original.symm.trans d.original ∈ piecewiseAffineGroupoid M) :
    c.chart.symm.trans d.chart ∈ piecewiseAffineGroupoid M := by
  let T := c.original.symm.trans d.original
  let H := c.chart.symm.trans d.chart
  let a := ContinuousLinearMap.fst ℝ ℝ E
  let v : M := (1, 0)
  let Z : M →L[ℝ] M := ContinuousLinearMap.id ℝ M - a.smulRight v
  have hZ (p : M) : Z p = (0, p.2) := by
    apply Prod.ext <;> simp [Z, a, v]
  have hT : LocallyPiecewiseAffineOn T T.source :=
    (mem_piecewiseAffineGroupoid_iff_forward _).mp hcompat
  have hzero : ∀ p ∈ T.source, a p = 0 → a (T p) = 0 := by
    intro p hp hp0
    have hc := original_frontier c.original c.original_side
      (c.original.symm p) (c.original.map_target hp.1)
    rw [c.original.right_inv hp.1] at hc
    have hd := original_frontier d.original d.original_side (c.original.symm p) hp.2
    exact hd.mp (hc.mpr hp0)
  let W := Z ⁻¹' T.source
  have hW : IsOpen W := T.open_source.preimage Z.continuous
  have hTZ : LocallyPiecewiseAffineOn (T ∘ Z) W := by
    have h := hT.comp (locallyPiecewiseAffineOn_affine Z.toContinuousAffineMap isOpen_univ)
    change LocallyPiecewiseAffineOn (T ∘ Z) (univ ∩ W) at h
    simpa only [univ_inter] using h
  have hsecond : LocallyPiecewiseAffineOn (fun p => (T (Z p)).2) W := by
    have h := (locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap isOpen_univ).comp hTZ
    change LocallyPiecewiseAffineOn (fun p => (T (Z p)).2)
      (W ∩ (T ∘ Z) ⁻¹' univ) at h
    simpa only [preimage_univ, inter_univ, Function.comp_def] using h
  have hnegative : LocallyPiecewiseAffineOn
      (fun p : M => (p.1, (T (0, p.2)).2)) W := by
    apply ((locallyPiecewiseAffineOn_affine a.toContinuousAffineMap hW).prod_mk hsecond).congr
    intro p _
    change (p.1, (T (Z p)).2) = (p.1, (T (0, p.2)).2)
    rw [hZ]
  have hpaste : LocallyPiecewiseAffineOn
      (fun p : M => if 0 ≤ p.1 then T p else (p.1, (T (0, p.2)).2))
      (T.source ∩ W) := by
    have h := hT.collar_transition a v hzero
    change LocallyPiecewiseAffineOn
      (fun p => if 0 ≤ p.1 then T p else a p • v + Z (T (Z p))) (T.source ∩ W) at h
    apply h.congr
    intro p _
    by_cases ht : 0 ≤ p.1
    · simp only [if_pos ht]
    · simp only [if_neg ht]
      rw [hZ, hZ]
      apply Prod.ext <;> simp [a, v]
  have hpos : LocallyPiecewiseAffineOn H (H.source ∩ {p : M | 0 < p.1}) := by
    apply (hT.mono (H.open_source.inter (isOpen_lt continuous_const continuous_fst))
      (fun p hp => (c.transition_nonneg d hg p hp.1 hp.2.le).1)).congr
    intro p hp
    exact (c.transition_nonneg d hg p hp.1 hp.2.le).2.symm
  have hneg : LocallyPiecewiseAffineOn H (H.source ∩ {p : M | p.1 < 0}) := by
    have hsub : H.source ∩ {p : M | p.1 < 0} ⊆ W := by
      intro p hp
      change Z p ∈ T.source
      rw [hZ]
      exact (c.transition_nonpos d hg hinj p hp.1 hp.2.le).1
    apply (hnegative.mono (H.open_source.inter
      (isOpen_lt continuous_fst continuous_const)) hsub).congr
    intro p hp
    exact (c.transition_nonpos d hg hinj p hp.1 hp.2.le).2.symm
  have hnear : LocallyPiecewiseAffineOn H (H.source ∩ (T.source ∩ W)) := by
    apply (hpaste.mono (H.open_source.inter (T.open_source.inter hW)) inter_subset_right).congr
    intro p hp
    dsimp only
    by_cases ht : 0 ≤ p.1
    · rw [if_pos ht]
      exact (c.transition_nonneg d hg p hp.1 ht).2.symm
    · rw [if_neg ht]
      exact (c.transition_nonpos d hg hinj p hp.1 (lt_of_not_ge ht).le).2.symm
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro p hp
  by_cases hp0 : 0 < p.1
  · exact ⟨{p : M | 0 < p.1}, hp0, hpos⟩
  by_cases hp1 : p.1 < 0
  · exact ⟨{p : M | p.1 < 0}, hp1, hneg⟩
  have hpzero : p.1 = 0 := le_antisymm (le_of_not_gt hp0) (le_of_not_gt hp1)
  have hpT : p ∈ T.source := (c.transition_nonneg d hg p hp hpzero.ge).1
  refine ⟨T.source ∩ W, ⟨hpT, ?_⟩, hnear⟩
  change Z p ∈ T.source
  rw [hZ]
  have heq : (0, p.2) = p := Prod.ext hpzero.symm rfl
  rw [heq]
  exact hpT

end PoincareConjecture.M76.HamiltonMarkedCapCoordinates
