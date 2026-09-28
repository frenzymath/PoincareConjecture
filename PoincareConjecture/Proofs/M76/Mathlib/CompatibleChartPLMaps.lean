import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem locallyPiecewiseAffineOn_compatible_chart
    {M E F ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {f : M → F}
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (A : OpenPartialHomeomorph M E)
    (hA : ∀ i, (e i).symm.trans A ∈ piecewiseAffineGroupoid E) :
    LocallyPiecewiseAffineOn (f ∘ A.symm) A.target := by
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨i, hi⟩ := hcover (A.symm x)
  let T := A.symm.trans (e i)
  have hT : T ∈ piecewiseAffineGroupoid E := by
    simpa only [T, trans_symm_eq_symm_trans_symm, symm_symm] using
      (piecewiseAffineGroupoid E).symm (hA i)
  have hcomp : LocallyPiecewiseAffineOn ((f ∘ (e i).symm) ∘ T) T.source :=
    ((hf i).comp ((mem_piecewiseAffineGroupoid_iff E T).mp hT).1).mono
      T.open_source (fun y hy => ⟨hy, (e i).mapsTo hy.2⟩)
  have hlocal : LocallyPiecewiseAffineOn (f ∘ A.symm) T.source := by
    apply hcomp.congr
    intro y hy
    change f ((e i).symm ((e i) (A.symm y))) = f (A.symm y)
    have hyi : A.symm y ∈ (e i).source := hy.2
    exact congrArg f ((e i).left_inv hyi)
  exact ⟨T.source, ⟨hx, hi⟩,
    hlocal.mono (A.open_target.inter T.open_source) inter_subset_right⟩

end OpenPartialHomeomorph
