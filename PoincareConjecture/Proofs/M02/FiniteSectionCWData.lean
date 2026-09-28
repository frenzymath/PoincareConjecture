import PoincareConjecture.Proofs.M02.FiniteSectionCW

set_option autoImplicit false

open Set Metric Topology

universe u

namespace PoincareConjecture.Proofs.M02

theorem exists_finite_cwComplex_of_finite_section
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (S : Set F) (K : Geometry.SimplicialComplex ℝ F) (hfinite : K.faces.Finite)
    (dim : Finset F → ℕ)
    (hdim : ∀ s ∈ K.faces, ∀ t ∈ K.faces, t ⊂ s →
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F))).Nonempty →
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set F))).Nonempty → dim t < dim s)
    (hmaps : ∀ s ∈ K.faces,
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F))).Nonempty →
      ∃ e : PartialEquiv (Fin (dim s) → ℝ) F,
        e.source = ball 0 1 ∧
        e.target = S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F)) ∧
        ContinuousOn e (closedBall 0 1) ∧ ContinuousOn e.symm e.target ∧
        e '' closedBall 0 1 = S ∩ convexHull ℝ (s : Set F) ∧
        e '' sphere 0 1 = S ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set F))) :
    ∃ C : CWComplex (S ∩ K.space),
      letI := C
      CWComplex.Finite (S ∩ K.space) := by
  classical
  refine ⟨exists_cwComplex_of_finite_section S K hfinite dim hdim hmaps, ?_⟩
  let C := exists_cwComplex_of_finite_section S K hfinite dim hdim hmaps
  let : Topology.CWComplex (S ∩ K.space) := C
  let : Finite K.faces := hfinite.to_subtype
  refine { eventually_isEmpty_cell := ?_, finite_cell := ?_ }
  · change ∀ᶠ n in Filter.atTop,
      IsEmpty ({s : {s : K.faces //
        (S ∩ intrinsicInterior ℝ (convexHull ℝ (s.val : Set F))).Nonempty} //
        dim s.val.val = n})
    refine Filter.eventually_atTop.mpr
      ⟨hfinite.toFinset.sup dim + 1, fun n hn => ⟨fun s => ?_⟩⟩
    have hbound : dim s.val.val.val ≤ hfinite.toFinset.sup dim :=
      Finset.le_sup (hfinite.mem_toFinset.mpr s.val.val.property)
    have hdegree := s.property
    omega
  · intro n
    change Finite ({s : {s : K.faces //
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (s.val : Set F))).Nonempty} //
      dim s.val.val = n})
    infer_instance

end PoincareConjecture.Proofs.M02
