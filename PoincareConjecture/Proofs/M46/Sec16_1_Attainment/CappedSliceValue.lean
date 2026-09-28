import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SliceMinimum

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}

noncomputable def cappedSliceAction
    (G : GeneralizedLGeometryTransport 3 X time I) (T : ℝ) (x : G.Point)
    (barrier b : ℝ) : ℝ :=
  sInf (insert barrier {a | ∃ y : G.Point,
    ∃ p : M14BackwardPath G T 0 (b ^ 2) x y, M14BackwardLAction G p = a})

theorem cappedSliceAction_eq_of_minimum {barrier b : ℝ} {y : G.Point}
    (p : M14BackwardPath G T 0 (b ^ 2) x y)
    (hpB : M14BackwardLAction G p ≤ barrier)
    (hmin : ∀ z : G.Point, ∀ q : M14BackwardPath G T 0 (b ^ 2) x z,
      M14BackwardLAction G p ≤ M14BackwardLAction G q) :
    cappedSliceAction G T x barrier b = M14BackwardLAction G p := by
  apply IsLeast.csInf_eq
  refine ⟨Or.inr ⟨y, p, rfl⟩, ?_⟩
  intro a ha
  rcases ha with rfl | ⟨z, q, rfl⟩
  · exact hpB
  · exact hmin z q

theorem cappedSliceAction_eq_barrier {barrier b : ℝ}
    (hmin : ∀ z : G.Point, ∀ q : M14BackwardPath G T 0 (b ^ 2) x z,
      barrier ≤ M14BackwardLAction G q) :
    cappedSliceAction G T x barrier b = barrier := by
  apply IsLeast.csInf_eq
  refine ⟨Or.inl rfl, ?_⟩
  intro a ha
  rcases ha with rfl | ⟨z, q, rfl⟩
  · exact le_rfl
  · exact hmin z q

theorem cappedSliceAction_alternative
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    {b : ℝ} (hb : 0 < b) (hbStart : b ^ 2 ≤ T - start) :
    cappedSliceAction G T x C.barrier b ≤ C.barrier ∧
      (∀ z : G.Point, ∀ q : M14BackwardPath G T 0 (b ^ 2) x z,
        cappedSliceAction G T x C.barrier b ≤ M14BackwardLAction G q) ∧
      (cappedSliceAction G T x C.barrier b = C.barrier ∨
        ∃ y : G.Point, ∃ p : M14BackwardPath G T 0 (b ^ 2) x y,
          M14IsMinimizing p ∧
          M14BackwardLAction G p = cappedSliceAction G T x C.barrier b ∧
          M14BackwardLAction G p < C.barrier ∧
          ∀ z : G.Point, ∀ q : M14BackwardPath G T 0 (b ^ 2) x z,
            M14BackwardLAction G p ≤ M14BackwardLAction G q) := by
  classical
  by_cases hreach : ∃ y : G.Point, ∃ p : M14BackwardPath G T 0 (b ^ 2) x y,
      M14BackwardLAction G p < C.barrier
  · obtain ⟨y0, p0, hp0⟩ := hreach
    obtain ⟨y, p, hp, hpp0, hmin⟩ :=
      exists_confined_slice_minimum hM04 hM12 LG E C hb hbStart p0 hp0
    have hpB := hpp0.trans_lt hp0
    have heq := cappedSliceAction_eq_of_minimum p hpB.le hmin
    exact ⟨heq.le.trans hpB.le, fun z q => heq.le.trans (hmin z q),
      Or.inr ⟨y, p, hp, heq.symm, hpB, hmin⟩⟩
  · have hmin (z : G.Point) (q : M14BackwardPath G T 0 (b ^ 2) x z) :
        C.barrier ≤ M14BackwardLAction G q :=
      le_of_not_gt (fun hq => hreach ⟨z, q, hq⟩)
    have heq := cappedSliceAction_eq_barrier hmin
    exact ⟨heq.le, fun z q => heq.le.trans (hmin z q), Or.inl heq⟩

theorem cappedSliceAction_exponential
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    {b : ℝ} (hb : 0 < b) (hbStart : b ^ 2 ≤ T - start)
    (hvalue : cappedSliceAction G T x C.barrier b < C.barrier) :
    ∃ Z : G.Horizontal x, ∃ hZ : (Z, b) ∈ E.domain,
      M14IsMinimizing (E.path Z b hZ hb) ∧
      E.action Z b = cappedSliceAction G T x C.barrier b := by
  obtain h | ⟨y, p, hp, haction, _, _⟩ :=
    (cappedSliceAction_alternative hM04 hM12 LG E C hb hbStart).2.2
  · exact False.elim ((ne_of_lt hvalue) h)
  obtain ⟨Z, hZsqrt, htrace, _⟩ := minimizing_exponential_branch LG E p hp
  have hZ : (Z, b) ∈ E.domain := by simpa only [Real.sqrt_sq hb.le] using hZsqrt
  obtain ⟨hact, hminimal⟩ := represented_minimizer_action E hb p hZ htrace
  exact ⟨Z, hZ, hminimal.mp hp, hact.trans haction⟩

end PoincareConjecture.Proofs.M46
