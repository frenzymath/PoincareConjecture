import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Augmented

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber
private theorem mfderiv_cons_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {k : ℕ}
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ)
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) x v =
      Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x v) := by
  have hcons (i : Fin (k + 1)) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y) i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using hφ
    · simpa only [Fin.cons_succ] using contMDiff_pi_space.mp hf j
  apply funext
  intro i
  rw [Poincare.Geometry.Manifold.mfderiv_pi_apply
    (fun i y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y) i) hcons]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact (Poincare.Geometry.Manifold.mfderiv_pi_apply
      (fun i y => f y i) (contMDiff_pi_space.mp hf) x v j).symm

theorem surjective_mfderiv_of_surjective_cons
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {k : ℕ}
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ)
    (x : M)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) x)) :
    Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x) := by
  intro z
  obtain ⟨v, hv⟩ := hreg (Fin.cons (α := fun _ : Fin (k + 1) => ℝ) 0 z)
  rw [mfderiv_cons_apply hf hφ] at hv
  exact ⟨v, funext (fun i => by simpa using congrFun hv i.succ)⟩

theorem regular_openFiber_restriction_of_surjective_mfderiv_cons
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {m k : ℕ} [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ)
    (U : Opens M)
    (hreg : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (x : openFiber f U c)
    (haug : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y))
      (openFiberIncl f U c x))) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    mfderiv (𝓡 m) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x ≠ 0 := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  change mfderiv (𝓡 m) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x ≠ 0
  obtain ⟨v, hv⟩ := haug (Fin.cons (α := fun _ : Fin (k + 1) => ℝ) 1 0)
  rw [mfderiv_cons_apply hf hφ] at hv
  have hvφ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ (openFiberIncl f U c x) v = (1 : ℝ) := by
    simpa using congrFun hv 0
  have hvf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f (openFiberIncl f U c x) v = 0 :=
    funext (fun i => by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f (openFiberIncl f U c x) v i = (0 : ℝ)
      simpa using congrFun hv i.succ)
  have hvker : v ∈ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f
      (openFiberIncl f U c x)).ker := hvf
  rw [← range_mfderiv_openFiberIncl (m := m) hf U hreg c x] at hvker
  obtain ⟨w, hw⟩ := hvker
  intro hzero
  have hw1 : mfderiv (𝓡 m) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x w = (1 : ℝ) := by
    rw [mfderiv_comp x ((hφ _).mdifferentiableAt (by simp))
      ((contMDiff_openFiberIncl hf U hreg c x).mdifferentiableAt (by simp))]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ (openFiberIncl f U c x)
      (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x w) = (1 : ℝ)
    exact (congrArg (fun v => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ
      (openFiberIncl f U c x) v) hw).trans hvφ
  rw [hzero] at hw1
  have : (0 : ℝ) = 1 := hw1
  norm_num at this
end Poincare.Geometry.Manifold.RegularFiber
