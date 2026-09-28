import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A F : Type*} [TopologicalSpace A] [FirstCountableTopology A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem spatial_jets_jointly_continuous_of_uniform_bounds
    {f : A → V → F}
    (hc : Continuous (fun p : A × V => f p.1 p.2))
    (hs : ∀ a, ContDiff ℝ ∞ (f a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C)
    (j : ℕ) : Continuous (fun p : A × V => iteratedFDeriv ℝ j (f p.1) p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro p p₀ hp
  have ht : Tendsto (fun k => (p k).1) atTop (𝓝 p₀.1) :=
    (continuous_fst.tendsto p₀).comp hp
  have hx : Tendsto (fun k => (p k).2) atTop (𝓝 p₀.2) :=
    (continuous_snd.tendsto p₀).comp hp
  have hpoint (x : V) (_hx : x ∈ (univ : Set V)) :
      Tendsto (fun k => f (p k).1 x) atTop (𝓝 (f p₀.1 x)) := by
    have hprod : Tendsto (fun k => ((p k).1, x)) atTop (𝓝 (p₀.1, x)) :=
      ht.prodMk_nhds tendsto_const_nhds
    simpa only [Function.comp_def] using (hc.tendsto (p₀.1, x)).comp hprod
  have hj :=
    tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth hpoint
      (fun x _ => ⟨univ, isOpen_univ, mem_univ x, subset_rfl,
        Eventually.of_forall (fun k => (hs (p k).1).contDiffOn)⟩)
      (fun _ _ _ m => by
        obtain ⟨C, hC⟩ := hb m
        exact ⟨C, Eventually.of_forall (fun k x _ => hC (p k).1 x)⟩) j
  exact hj.tendsto_comp
    ((hs p₀.1).continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).continuousAt.continuousWithinAt
    (mem_univ _) (by simpa only [nhdsWithin_univ] using hx)

theorem spatial_fderiv_jointly_continuous_of_uniform_bounds
    {f : A → V → F}
    (hc : Continuous (fun p : A × V => f p.1 p.2))
    (hs : ∀ a, ContDiff ℝ ∞ (f a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) :
    Continuous (fun p : A × V => fderiv ℝ (f p.1) p.2) := by
  have h := (continuousMultilinearCurryFin1 ℝ V F).continuous.comp
    (spatial_jets_jointly_continuous_of_uniform_bounds hc hs hb 1)
  have heq : (fun p : A × V =>
      continuousMultilinearCurryFin1 ℝ V F (iteratedFDeriv ℝ 1 (f p.1) p.2)) =
      fun p => fderiv ℝ (f p.1) p.2 := by
    funext p
    ext v
    simp only [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    congr 1
  exact heq ▸ h

end PoincareConjecture.M35.RadialGauge
