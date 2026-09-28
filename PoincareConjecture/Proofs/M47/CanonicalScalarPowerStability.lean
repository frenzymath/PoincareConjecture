import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem continuousAt_scalarPower_extrema_on_compact
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J)
    (t : J) {K : Set M} (hK : IsCompact K)
    (hpositive : ∀ x ∈ K, 0 < (F.connection t.val).scalarCurvature x) (p : ℝ) :
    ContinuousAt (fun s : J => sSup (range (fun x : K =>
      (F.connection s.val).scalarCurvature x.val ^ p))) t ∧
    ContinuousAt (fun s : J => sInf (range (fun x : K =>
      (F.connection s.val).scalarCurvature x.val ^ p))) t := by
  have hscalar : Continuous (fun z : J × M =>
      (F.connection z.1.val).scalarCurvature z.2) := by
    have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) := by fun_prop
    have h := (hC.scalar_regular 3 M J F).continuousOn.comp_continuous hmap
      (fun z => ⟨z.1.property, mem_univ z.2⟩)
    exact h
  have hslice : Continuous (F.connection t.val).scalarCurvature := by
    have h := hscalar.comp (continuous_const.prodMk continuous_id :
      Continuous (fun x : M => (t, x)))
    exact h
  obtain ⟨m, hm, hfloor⟩ := hK.exists_forall_le' hslice.continuousOn hpositive
  let G : J → M → ℝ := fun s x =>
    (max (m / 2) ((F.connection s.val).scalarCurvature x)) ^ p
  have hG : Continuous (Function.uncurry G) :=
    (continuous_const.max hscalar).rpow_const (fun z =>
      Or.inl (ne_of_gt ((half_pos hm).trans_le (le_max_left _ _))))
  have hsame : ∀ᶠ s : J in 𝓝 t, ∀ x ∈ K,
      G s x = (F.connection s.val).scalarCurvature x ^ p := by
    filter_upwards [scalar_uniform_near_time_on_compact hC F hK t (half_pos hm)]
      with s hs
    intro x hx
    have hbound : m / 2 < (F.connection s.val).scalarCurvature x := by
      have hdiff := (abs_lt.mp (hs x hx)).1
      linarith [hfloor x hx]
    dsimp only [G]
    rw [max_eq_right hbound.le]
  have hsup : Continuous (fun s : J => sSup (range (fun x : K => G s x.val))) := by
    simpa only [image_eq_range] using hK.continuous_sSup hG
  have hinf : Continuous (fun s : J => sInf (range (fun x : K => G s x.val))) := by
    simpa only [image_eq_range] using hK.continuous_sInf hG
  constructor
  · apply hsup.continuousAt.congr_of_eventuallyEq
    filter_upwards [hsame] with s hs
    congr 2
    funext x
    exact (hs x.val x.property).symm
  · apply hinf.continuousAt.congr_of_eventuallyEq
    filter_upwards [hsame] with s hs
    congr 2
    funext x
    exact (hs x.val x.property).symm

end PoincareConjecture.Proofs.M47
