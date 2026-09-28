import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
namespace Poincare.Geometry.Manifold.RegularFiber

private theorem surjective_cons_of_surjective_of_exists_ker
    {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (A : E →ₗ[ℝ] (Fin k → ℝ)) (B : E →ₗ[ℝ] ℝ) (hA : Surjective A)
    (hB : ∃ w, A w = 0 ∧ B w ≠ 0) :
    Surjective (fun v => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (B v) (A v)) := by
  intro z
  obtain ⟨v, hv⟩ := hA (fun i => z i.succ)
  obtain ⟨w, hw, hBw⟩ := hB
  refine ⟨v + ((z 0 - B v) / B w) • w, ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  · simp [hv, hw]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {k : ℕ} {f : M → Fin k → ℝ} {φ : M → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f)
  (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ)

include hf hφ in

theorem surjective_mfderiv_cons_of_exists_ker (x : M)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (hφker : ∃ w : TangentSpace 𝓘(ℝ, E) x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x w = 0 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x w ≠ 0) :
    Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) x) := by
  have h := surjective_cons_of_surjective_of_exists_ker
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x).toLinearMap
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x).toLinearMap hreg hφker
  have hcons (i : Fin (k + 1)) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y) i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using hφ
    · simpa only [Fin.cons_succ] using contMDiff_pi_space.mp hf j
  convert! h using 1
  funext w i
  rw [Poincare.Geometry.Manifold.mfderiv_pi_apply
    (fun i y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y) i) hcons]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have he := (Poincare.Geometry.Manifold.mfderiv_pi_apply
        (fun i y => f y i) (contMDiff_pi_space.mp hf) x w j).symm
    change mvfderiv 𝓘(ℝ, E) (fun y => f y j) x w =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x) w j at he
    exact he

include hφ in

theorem surjective_mfderiv_cons_of_regular_openFiber_restriction
    {m : ℕ} [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (U : Opens M)
    (hreg : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (x : openFiber f U c) :
    let := openFiberChartedSpace (m := m) hf U hreg c
    mfderiv (𝓡 m) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x ≠ 0 →
      Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
        (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) (openFiberIncl f U c x)) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  dsimp only
  intro hφreg
  apply surjective_mfderiv_cons_of_exists_ker hf hφ (openFiberIncl f U c x)
    (hreg _ (x : U).2)
  have hw : ∃ w : TangentSpace (𝓡 m) x,
      mfderiv (𝓡 m) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x w ≠ 0 := by
    by_contra! h
    apply hφreg
    ext w
    exact h w
  obtain ⟨w, hw⟩ := hw
  refine ⟨mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x w, ?_, ?_⟩
  · have hr := range_mfderiv_openFiberIncl (m := m) hf U hreg c x
    have hm : mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x w ∈
        (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x).range := ⟨w, rfl⟩
    rw [hr] at hm
    exact hm
  · rwa [mfderiv_comp x ((hφ _).mdifferentiableAt (by simp))
      ((contMDiff_openFiberIncl hf U hreg c x).mdifferentiableAt (by simp))] at hw

end Poincare.Geometry.Manifold.RegularFiber
