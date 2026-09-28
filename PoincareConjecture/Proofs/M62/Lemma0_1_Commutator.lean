import PoincareConjecture.Proofs.M62.Lemma0_1_SpeedEvolution
import PoincareConjecture.Proofs.M62.Mathlib.MixedDerivatives
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem arc_time_commutator (hc : M62ShrinkingCurve F c)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.univ ×ˢ Set.Ioo a b))
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    deriv (fun s ↦ m62ArcDerivative F c s (fun y ↦ f (y, s)) x) t -
      m62ArcDerivative F c t (fun y ↦ deriv (fun s ↦ f (y, s)) t) x =
        (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          m62ArcDerivative F c t (fun y ↦ f (y, t)) x := by
  have hmem : (x, t) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) := ⟨Set.mem_univ _, ht⟩
  have hfat := (hf (x, t) hmem).contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)
  obtain ⟨k, htime, hspace⟩ := hfat.exists_hasDerivAt_mixed
  have hv := (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x).ne'
  have hinv := (hasDerivAt_speed F c hc ht x).fun_inv hv
  have hprod := hinv.fun_mul htime
  change deriv (fun s ↦ (curveSpeed F c s x)⁻¹ * deriv (fun y ↦ f (y, s)) x) t -
    (curveSpeed F c t x)⁻¹ * deriv (fun y ↦ deriv (fun s ↦ f (y, s)) t) x = _
  rw [hprod.deriv, hspace.deriv]
  unfold m62ArcDerivative
  field_simp
  ring

end PoincareConjecture.M62
