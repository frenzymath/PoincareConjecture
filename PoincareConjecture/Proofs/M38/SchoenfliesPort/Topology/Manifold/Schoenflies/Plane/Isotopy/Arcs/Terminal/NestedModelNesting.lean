import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelMarkedCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CircleComponents
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleMatching

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private def shiftHeight (c : Real) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun y := y - c • (EuclideanSpace.single 2 1 : E3)
  invFun y := y + c • (EuclideanSpace.single 2 1 : E3)
  left_inv y := by simp
  right_inv y := by simp
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem exists_nested_model_lower_slice_fillings
    (d : TerminalSaddleGeometry M P p e)
    (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ C : Fin 2 → S1 → E2,
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        Disjoint (range (C 0)) (range (C 1)) ∧
        (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
        NestedPair (C 1) (C 0) := by
  let c := inner Real (M.v : E3) (g p)
  let S := shiftHeight c
  let T := (d.transport.trans d.flatten).trans S
  have hc := terminal_model_chart_critical d hform
  rw [hmodel] at hc
  have hTheight (y : E3) : T y 2 =
      d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) := by
    change (d.frame (d.D (d.transport y)) - c • (EuclideanSpace.single 2 1 : E3)) 2 = _
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
      mul_one]
    rw [d.frame_height, d.D_height, d.transport_height, hmodel]
    change c + d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) - c = _
    ring
  obtain ⟨ε, hε, hcircles⟩ := Saddle.Nested.exists_uniform_negative_nested_level_circles
    T (Diffeomorph.refl (𝓡 3) E3 (n := ∞)) (fun _ => rfl) hc
    (terminal_nested_model_chart_latitude d hmodel hform) d.scale_pos hTheight
  refine ⟨ε, hε, ?_⟩
  intro t ht
  obtain ⟨C, hC, _, hdis, hcover, A, B, hA, hB, hBA⟩ :=
    hcircles (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hS (x : E2) : S (Saddle.toE3 x (c - t)) = Saddle.toE3 x (-t) := by
    change Saddle.toE3 x (c - t) - c • EuclideanSpace.single 2 1 = Saddle.toE3 x (-t)
    ext i
    fin_cases i <;> simp [Saddle.toE3]
  refine ⟨C, hC, hdis, hcover.trans ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨d.transport (d.model y), ⟨y, hy, rfl⟩, ?_⟩
      apply S.injective
      change S (d.flatten (d.transport (d.model y))) = S (Saddle.toE3 x (c - t))
      rw [hS, hmodel]
      exact heq
    · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
      change d.flatten (d.transport (d.model y)) = Saddle.toE3 x (c - t) at heq
      refine ⟨y, hy, ?_⟩
      change S (d.flatten (d.transport (Saddle.Nested.shear (3 / 10) y))) = _
      rw [← hmodel, heq, hS]
  · exact (nestedPair_iff_of_normalizations (C 1) (C 0) B A hB hA).mpr hBA

private theorem nesting_or_reverse_of_equal_pair_union
    (C D : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i)) (hD : ∀ i, Continuous (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hunion : (⋃ i, range (C i)) = ⋃ i, range (D i))
    (hnest : NestedPair (D 1) (D 0)) :
    NestedPair (C 0) (C 1) ∨ NestedPair (C 1) (C 0) := by
  obtain ⟨E, hE⟩ := exists_circle_pair_range_permutation C D hC hD hCdis hDdis hunion
  have hn : NestedPair (C (E.symm 1)) (C (E.symm 0)) := by
    rcases hnest with ⟨A, hA, hin⟩
    refine ⟨A, ?_, ?_⟩
    · simpa only [hE, E.apply_symm_apply] using hA
    · simpa only [hE, E.apply_symm_apply] using hin
  have hne : E.symm 1 ≠ E.symm 0 := E.symm.injective.ne (by decide)
  generalize h1 : E.symm 1 = i at hn hne
  generalize h0 : E.symm 0 = j at hn hne
  fin_cases i <;> fin_cases j
  · exact (hne rfl).elim
  · exact Or.inl hn
  · exact Or.inr hn
  · exact (hne rfl).elim

theorem exists_nested_model_negative_branch_circle_pairs
    (d : TerminalSaddleGeometry M P p e)
    (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < d.eta ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ C : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
          Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
          (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
          (∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
            Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i)) ∧
          (NestedPair (C 0) (C 1) ∨ NestedPair (C 1) (C 0)) := by
  obtain ⟨r, δ, hr, hrs, hδ, hδη, hδr, hmarked⟩ :=
    exists_model_negative_branch_circle_pairs d hform
  obtain ⟨ε, hε, hnested⟩ := exists_nested_model_lower_slice_fillings d hmodel hform
  refine ⟨r, min δ ε, hr, hrs, lt_min hδ hε,
    (min_le_left _ _).trans_lt hδη, (min_le_left _ _).trans_lt hδr, ?_⟩
  intro t ht
  obtain ⟨C, hC, hi, hcover, hbranch⟩ :=
    hmarked t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  obtain ⟨D, hD, hDdis, hDcover, hnest⟩ :=
    hnested t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have hCdis : Disjoint (range (C 0)) (range (C 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨q, hq⟩ ⟨u, hu⟩
    have heq := congrArg Prod.fst (hi (a₁ := (0, q)) (a₂ := (1, u)) (hq.trans hu.symm))
    exact (by decide : (0 : Fin 2) ≠ 1) heq
  exact ⟨C, hC, hi, hcover, hbranch,
    nesting_or_reverse_of_equal_pair_union C D (fun i => (hC i).contMDiff.continuous)
      (fun i => (hD i).contMDiff.continuous) hCdis hDdis (hcover.trans hDcover.symm) hnest⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
