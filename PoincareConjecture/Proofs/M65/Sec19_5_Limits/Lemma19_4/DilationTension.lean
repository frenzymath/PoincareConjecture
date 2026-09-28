import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskDilation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65PlaneTension_diskDilation {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : LoopPlane → M) (r : ℝ) (z : LoopPlane)
    (hf : ContMDiffAt (𝓡 2) (𝓡 n) ∞ f (r • z)) :
    m65PlaneTension D (fun w => f (r • w)) z = r ^ 2 • m65PlaneTension D f (r • z) := by
  unfold m65PlaneTension
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  let γ : ℝ → M := fun s => f (r • z + s • v)
  let Y : (s : ℝ) → TangentSpace (𝓡 n) (γ s) :=
    fun s => mfderiv (𝓡 2) (𝓡 n) f (r • z + s • v) v
  let φ : ℝ → ℝ := fun s => r * s
  have hzero : r • z + (0 : ℝ) • v = r • z := by simp
  have hY : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)) 0 := by
    have hc := RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v
    have hc' : ContMDiffAt (𝓡 2) ((𝓡 n).prod (𝓡 n)) ∞
        (fun w => (⟨f w, mfderiv (𝓡 2) (𝓡 n) f w v⟩ : TangentBundle (𝓡 n) M))
        (r • z + (0 : ℝ) • v) := by simpa only [hzero] using hc
    have hline : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun s : ℝ => r • z + s • v) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    exact (hc'.comp 0 hline.contMDiffAt).mdifferentiableAt (by simp)
  have hφ : HasDerivAt φ r 0 := by
    simpa +instances only [φ, mul_one] using! (hasDerivAt_id (0 : ℝ)).const_mul r
  have hYφ : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)) (φ 0) := by
    simpa only [φ, mul_zero] using hY
  have hchain := m65Pullback_fixed_relabeling D hYφ hφ
  have hscale := M62.pullback_smul D (γ := γ ∘ φ) (Y := fun s => Y (φ s))
    (hasDerivAt_const (0 : ℝ) r) (hYφ.comp 0 hφ.differentiableAt.mdifferentiableAt)
  have hpoint : φ 0 = 0 := by simp [φ]
  rw [zero_smul, zero_add, hchain, hpoint, smul_smul, ← pow_two] at hscale
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), MDifferentiableAt (𝓡 2) (𝓡 n) f
      (r • (z + s • v)) := by
    have hcont : ContinuousAt (fun s : ℝ => r • (z + s • v)) 0 := by fun_prop
    have hnear' := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp
      (hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from by simp))
    have h := hcont.eventually (by simpa only [zero_smul, add_zero] using hnear')
    filter_upwards [h] with s hs
    exact hs.mdifferentiableAt (by decide)
  have hcongr := M62.pullback_congr D
    (γ := fun s : ℝ => f (r • (z + s • v)))
    (Y := fun s => mfderiv (𝓡 2) (𝓡 n) (fun w => f (r • w)) (z + s • v) v)
    (Z := fun s => r • mfderiv (𝓡 2) (𝓡 n) f (r • (z + s • v)) v)
    (hnear.mono fun s hs => m65Mfderiv_diskDilation f r (z + s • v) v hs)
  apply hcongr.trans
  have harg : (fun s : ℝ => r • (z + s • v)) = fun s : ℝ => r • z + (r * s) • v := by
    funext s
    rw [smul_add, smul_smul]
  change rampHorizontalCovariantDerivative D (f ∘ fun s : ℝ => r • (z + s • v))
    (fun s => r • mfderiv (𝓡 2) (𝓡 n) f ((fun q : ℝ => r • (z + q • v)) s) v) 0 = _
  rw [harg]
  exact hscale

end PoincareConjecture
