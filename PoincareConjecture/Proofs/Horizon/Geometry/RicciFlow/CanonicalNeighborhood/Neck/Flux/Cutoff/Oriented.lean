import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Transition

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem axialTransition_one_sub_profile
    {A B : Set M} (hdisj : Disjoint A B)
    (hcover : A ∪ B = N.central_sphereᶜ) (φ : ℝ → ℝ) :
    N.axialTransition A (fun s => 1 - φ s) =
      fun x => 1 - N.axialTransition B φ x := by
  funext x
  by_cases hx : x ∈ N.carrier
  · simp only [N.axialTransition_eq_of_mem A _ hx,
      N.axialTransition_eq_of_mem B _ hx]
  · have hxside : x ∈ A ∪ B := by
      rw [hcover]
      exact fun h => hx (N.central_sphere_subset_carrier h)
    rcases hxside with hxA | hxB
    · have hxB : x ∉ B := fun h => Set.disjoint_left.mp hdisj hxA h
      simp [axialTransition, hx, hxA, hxB]
    · have hxA : x ∉ A := fun h => Set.disjoint_left.mp hdisj h hxB
      simp [axialTransition, hx, hxA, hxB]

theorem contMDiff_axialTransition_one_sub_profile
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ B)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ A)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hzero : ∀ s ≤ -L, φ s = 0)
    (hone : ∀ s, L ≤ s → φ s = 1) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N.axialTransition A (fun s => 1 - φ s)) := by
  rw [N.axialTransition_one_sub_profile hdisj hcover]
  exact contMDiff_const.sub (N.contMDiff_axialTransition hB hA hdisj.symm
    ((union_comm B A).trans hcover) hneg hpos hL hLe hφ hzero hone)

theorem hasCompactSupport_one_sub_axialTransition_one_sub_profile
    {A B : Set M} (hAc : IsCompact (closure A))
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ A)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hzero : ∀ s ≤ -L, φ s = 0) :
    HasCompactSupport (fun x => 1 - N.axialTransition A (fun s => 1 - φ s) x) := by
  rw [N.axialTransition_one_sub_profile hdisj hcover]
  simp only [sub_sub_cancel]
  exact N.hasCompactSupport_axialTransition hAc hdisj.symm
    ((union_comm B A).trans hcover) hpos hL hLe hzero

theorem axialTransition_one_sub_profile_eventually_constant_of_not_mem
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ B)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ A)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hzero : ∀ s ≤ -L, φ s = 0) (hone : ∀ s, L ≤ s → φ s = 1)
    {x : M} (hx : x ∉ N.carrier) :
    ∃ c : ℝ, N.axialTransition A (fun s => 1 - φ s) =ᶠ[𝓝 x] fun _ => c := by
  obtain ⟨c, he⟩ := N.axialTransition_eventually_constant_of_not_mem hB hA
    hdisj.symm ((union_comm B A).trans hcover) hneg hpos hL hLe hzero hone hx
  refine ⟨1 - c, ?_⟩
  rw [N.axialTransition_one_sub_profile hdisj hcover]
  filter_upwards [he] with y hy
  rw [hy]

theorem exists_outward_axialTransition
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hhalf :
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
      (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A))
    (hAc : IsCompact (closure A))
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hrange : ∀ s, φ s ∈ Icc 0 1)
    (hzero : ∀ s ≤ -L, φ s = 0) (hone : ∀ s, L ≤ s → φ s = 1) :
    ∃ ψ : ℝ → ℝ,
      ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧ ψ = φ) ∨
        (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A ∧
          ψ = fun s => 1 - φ s)) ∧
      ContDiff ℝ ∞ ψ ∧ (∀ s, ψ s ∈ Icc 0 1) ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N.axialTransition A ψ) ∧
      HasCompactSupport (fun x => 1 - N.axialTransition A ψ x) ∧
      ∀ x ∉ N.carrier, ∃ c : ℝ, N.axialTransition A ψ =ᶠ[𝓝 x] fun _ => c := by
  rcases hhalf with ⟨hneg, hpos⟩ | ⟨hneg, hpos⟩
  · exact ⟨φ, Or.inl ⟨hneg, hpos, rfl⟩, hφ, hrange,
      N.contMDiff_axialTransition hA hB hdisj hcover hneg hpos hL hLe hφ hzero hone,
      N.hasCompactSupport_one_sub_axialTransition hAc hdisj hcover hneg hL hLe hone,
      fun _ hx => N.axialTransition_eventually_constant_of_not_mem hA hB hdisj hcover
        hneg hpos hL hLe hzero hone hx⟩
  · refine ⟨(fun s => 1 - φ s), Or.inr ⟨hneg, hpos, rfl⟩,
      contDiff_const.sub hφ, ?_,
      N.contMDiff_axialTransition_one_sub_profile hA hB hdisj hcover hneg hpos
        hL hLe hφ hzero hone,
      N.hasCompactSupport_one_sub_axialTransition_one_sub_profile hAc hdisj hcover hpos
        hL hLe hzero,
      fun _ hx => N.axialTransition_one_sub_profile_eventually_constant_of_not_mem
        hA hB hdisj hcover hneg hpos hL hLe hzero hone hx⟩
    intro s
    exact ⟨sub_nonneg.mpr (hrange s).2, by linarith [(hrange s).1]⟩

end PoincareConjecture.EpsilonNeck
