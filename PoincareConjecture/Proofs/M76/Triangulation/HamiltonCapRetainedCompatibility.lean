import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedCapCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.Algebra.ContinuousAffineEquiv









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonMarkedCapCoordinates

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {D S : Set X} {eps : ℝ} {g : S × Ico (0 : ℝ) eps → X}




theorem retained_compatible (c : HamiltonMarkedCapCoordinates (E := E) (D := D) g)
    (a q : (ℝ × E) ≃ᴬ[ℝ] F) (f : OpenPartialHomeomorph X F)
    (hcompat : (c.original.transHomeomorph a.toHomeomorph).symm.trans f ∈
      piecewiseAffineGroupoid F)
    (hD : IsClosed D) (hg : ∀ p, g p ∈ D) :
    (c.chart.transHomeomorph q.toHomeomorph).symm.trans
      (f.restrOpen Dᶜ hD.isOpen_compl) ∈ piecewiseAffineGroupoid F := by
  let B := c.original.transHomeomorph a.toHomeomorph
  let H := c.chart.transHomeomorph q.toHomeomorph
  let T := B.symm.trans f
  let Hf := H.symm.trans (f.restrOpen Dᶜ hD.isOpen_compl)
  let k : F →ᴬ[ℝ] F := a.toContinuousAffineMap.comp q.symm.toContinuousAffineMap
  have hT : LocallyPiecewiseAffineOn T T.source :=
    (mem_piecewiseAffineGroupoid_iff_forward _).mp hcompat
  have hpoint (p : F) (hp : p ∈ Hf.source) :
      k p ∈ T.source ∧ T (k p) = Hf p := by
    have hpq : q.symm p ∈ c.chart.target := hp.1
    have hx : c.chart.symm (q.symm p) ∈ c.chart.source := c.chart.map_target hpq
    have hxnot : c.chart.symm (q.symm p) ∉ D := hp.2.2
    have ht : 0 ≤ (q.symm p).1 := by
      by_contra hn
      apply hxnot
      apply (c.side hg _ hx).mpr
      rw [c.chart.right_inv hpq]
      exact (lt_of_not_ge hn).le
    have hinv := c.inverse_nonneg (q.symm p) hpq ht
    have hpB : q.symm p ∈ c.original.target := c.rectangle (c.target.subset hpq)
    have hBinv : B.symm (k p) = c.original.symm (q.symm p) := by
      change c.original.symm (a.symm (a (q.symm p))) = _
      rw [a.symm_apply_apply]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change a.symm (a (q.symm p)) ∈ c.original.target
      rw [a.symm_apply_apply]
      exact hpB
    · change B.symm (k p) ∈ f.source
      rw [hBinv, ← hinv]
      exact hp.2.1
    · change f (B.symm (k p)) = f (c.chart.symm (q.symm p))
      rw [hBinv, hinv]
  have hpre := hT.comp (locallyPiecewiseAffineOn_affine k isOpen_univ)
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply (hpre.mono Hf.open_source (fun p hp => ⟨mem_univ _, (hpoint p hp).1⟩)).congr
  intro p hp
  exact (hpoint p hp).2

end PoincareConjecture.M76.HamiltonMarkedCapCoordinates
