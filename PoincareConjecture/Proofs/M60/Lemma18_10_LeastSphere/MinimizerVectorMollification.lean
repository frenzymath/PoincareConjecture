import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakAverages
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.NonnegativeApproximation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.DifferenceQuotient

local notation "Plane" => EuclideanSpace ℝ (Fin 2)




theorem suEuclidean_Lp_tendsto_componentwise {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {v : ℕ → X → EuclideanSpace ℝ (Fin m)} {v0 : X → EuclideanSpace ℝ (Fin m)}
    (hv : ∀ j, AEStronglyMeasurable (v j) μ) (hv0 : AEStronglyMeasurable v0 μ)
    (hlim : ∀ a : Fin m, Tendsto
      (fun j => eLpNorm (fun x => v j x a - v0 x a) p μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (v j - v0) p μ) atTop (𝓝 0) := by
  let t : ℕ → Fin m → X → EuclideanSpace ℝ (Fin m) := fun j a x =>
    (v j x a - v0 x a) • EuclideanSpace.single a 1
  have ht (j : ℕ) (a : Fin m) : AEStronglyMeasurable (t j a) μ :=
    (((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_aestronglyMeasurable (hv j)).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_aestronglyMeasurable hv0)).smul_const _
  have hsum (j : ℕ) : v j - v0 = ∑ a : Fin m, t j a := by
    funext x
    apply PiLp.ext
    intro b
    rw [Finset.sum_apply]
    change v j x b - v0 x b = (EuclideanSpace.proj (𝕜 := ℝ) b) (∑ a : Fin m, t j a x)
    rw [map_sum]
    simp [t, PiLp.single_apply]
  have hn (j : ℕ) (a : Fin m) : eLpNorm (t j a) p μ =
      eLpNorm (fun x => v j x a - v0 x a) p μ :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp [t, norm_smul])
  have hb (j : ℕ) : eLpNorm (v j - v0) p μ ≤
      ∑ a : Fin m, eLpNorm (fun x => v j x a - v0 x a) p μ := by
    rw [hsum]
    exact (eLpNorm_sum_le (fun a _ => ht j a) hp).trans_eq (by simp only [hn])
  have hz : Tendsto (fun j => ∑ a : Fin m,
      eLpNorm (fun x => v j x a - v0 x a) p μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun a _ => hlim a)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => bot_le) hb




theorem suVectorMollifier_Lp_tendsto {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpf : p ≠ ⊤)
    {g : Plane → EuclideanSpace ℝ (Fin m)} (hg : MemLp g p volume)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hz : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      (fun x => (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] g) x - g x) p volume)
      atTop (𝓝 0) := by
  have hloc := hg.locallyIntegrable hp
  have hc (j) := (mollifierEps_compactSupport (hr j)).continuous_convolution_left
    (lsmul ℝ ℝ) (mollifierEps_continuous (hr j)) hloc
  apply suEuclidean_Lp_tendsto_componentwise hp (fun j => (hc j).aestronglyMeasurable) hg.1
  intro a
  have he (j : ℕ) (x : Plane) :
      (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] g) x a =
        mollifyEps (hr j) (fun y => g y a) x := by
    change (EuclideanSpace.proj (𝕜 := ℝ) a) (_) = _
    rw [suConvolution_map (mollifierEps_continuous (hr j))
      (mollifierEps_compactSupport (hr j)) hloc]
    rfl
  have hga : MemLp (fun x => g x a) p volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' hg
  simpa only [he] using tendsto_eLpNorm_mollifyEps_sub hr hz hp hpf hga

end PoincareConjecture.M60

end
