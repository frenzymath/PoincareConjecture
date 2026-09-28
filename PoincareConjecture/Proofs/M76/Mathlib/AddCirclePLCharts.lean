import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

theorem locallyPiecewiseAffineOn_toIcoMod {p : ℝ} (hp : 0 < p) (a : ℝ)
    {U : Set ℝ} (hU : IsOpen U)
    (hne : ∀ x ∈ U, (x : AddCircle p) ≠ (a : AddCircle p)) :
    LocallyPiecewiseAffineOn (toIcoMod hp a) U := by
  intro x hx
  have hdiv := eventuallyEq_toIcoDiv_nhds hp a (x := x)
    (AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr (hne x hx))
  obtain ⟨W, hWsub, hW, hxW⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hdiv)
  obtain ⟨K, hK, hxK, hKW⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton hW (singleton_subset_iff.mpr hxW)
  let b : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ -
    ContinuousAffineMap.const ℝ ℝ (toIcoDiv hp a x • p)
  refine ⟨K, hK, hxK (mem_singleton x), fun y hy => (hWsub (hKW hy)).1, ?_⟩
  apply (K.affineOnFaces_affine b).congr
  intro y hy
  change y - toIcoDiv hp a x • p = y - toIcoDiv hp a y • p
  rw [(hWsub (hKW hy)).2]

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

theorem quotient_chart_transition_locallyPiecewiseAffine (a b : ℝ) :
    LocallyPiecewiseAffineOn
      ((openPartialHomeomorphCoe p a).trans (openPartialHomeomorphCoe p b).symm)
      ((openPartialHomeomorphCoe p a).trans (openPartialHomeomorphCoe p b).symm).source := by
  let e := (openPartialHomeomorphCoe p a).trans (openPartialHomeomorphCoe p b).symm
  change LocallyPiecewiseAffineOn (toIcoMod (Fact.out : 0 < p) b) e.source
  apply locallyPiecewiseAffineOn_toIcoMod _ _ e.open_source
  intro x hx
  exact hx.2

theorem quotient_chart_transition_mem_piecewiseAffineGroupoid (a b : ℝ) :
    (openPartialHomeomorphCoe p a).trans (openPartialHomeomorphCoe p b).symm ∈
      piecewiseAffineGroupoid ℝ :=
  ⟨quotient_chart_transition_locallyPiecewiseAffine p a b,
    quotient_chart_transition_locallyPiecewiseAffine p b a⟩

theorem exists_core_fixed_puncturedCircle_chart (r : ℝ) (hr : r < p / 2) :
    ∃ e : OpenPartialHomeomorph (AddCircle p) ℝ,
      e.source = {((-p / 2 : ℝ) : AddCircle p)}ᶜ ∧
      e.target = Ioo (-p / 2) (p / 2) ∧
      (∀ x ∈ Icc (-r) r, (x : AddCircle p) ∈ e.source ∧ e x = x) ∧
      ∀ a : ℝ, (openPartialHomeomorphCoe p a).trans e ∈ piecewiseAffineGroupoid ℝ := by
  let e := (openPartialHomeomorphCoe p (-p / 2)).symm
  refine ⟨e, rfl, ?_, ?_, fun a =>
    quotient_chart_transition_mem_piecewiseAffineGroupoid p a (-p / 2)⟩
  · change Ioo (-p / 2) (-p / 2 + p) = Ioo (-p / 2) (p / 2)
    congr 1
    ring
  · intro x hx
    have hxsource : x ∈ (openPartialHomeomorphCoe p (-p / 2)).source := by
      change -p / 2 < x ∧ x < -p / 2 + p
      constructor <;> linarith [hx.1, hx.2]
    exact ⟨(openPartialHomeomorphCoe p (-p / 2)).mapsTo hxsource,
      (openPartialHomeomorphCoe p (-p / 2)).left_inv hxsource⟩

end AddCircle
