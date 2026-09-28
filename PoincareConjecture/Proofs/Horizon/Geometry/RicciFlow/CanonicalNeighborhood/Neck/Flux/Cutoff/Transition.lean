import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Profile










noncomputable section
set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



def axialTransition (A : Set M) (φ : ℝ → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ N.carrier then φ (N.coordinate_inverse x).2 else if x ∈ A then 0 else 1

theorem axialTransition_eq_of_mem (A : Set M) (φ : ℝ → ℝ)
    {x : M} (hx : x ∈ N.carrier) :
    N.axialTransition A φ x = φ (N.coordinate_inverse x).2 := by
  simp only [axialTransition, if_pos hx]

private theorem not_mem_coordinate_slab_of_not_mem_carrier
    {L : ℝ} (hL : L < N.epsilon⁻¹) {x : M} (hx : x ∉ N.carrier) :
    x ∉ N.coordinate_map '' (univ ×ˢ Icc (-L) L) := by
  rintro ⟨z, hz, rfl⟩
  exact hx (N.coordinate_map_mem ⟨mem_univ _, by linarith [hz.2.1],
    hz.2.2.trans_lt hL⟩)

private theorem axialTransition_eq_zero_on_negative_side
    {A B : Set M} (hdisj : Disjoint A B)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφ : ∀ s ≤ -L, φ s = 0) {x : M} (hxA : x ∈ A)
    (hxK : x ∉ N.coordinate_map '' (univ ×ˢ Icc (-L) L)) :
    N.axialTransition A φ x = 0 := by
  by_cases hx : x ∈ N.carrier
  · rw [N.axialTransition_eq_of_mem A φ hx]
    apply hφ
    have hs : (N.coordinate_inverse x).2 ≤ 0 := by
      by_contra hn
      exact Set.disjoint_left.mp hdisj hxA
        (hpos ⟨hx, lt_of_not_ge hn, (N.coordinate_inverse_mem x hx).2.2⟩)
    by_contra hn
    apply hxK
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, (lt_of_not_ge hn).le,
      hs.trans hL.le⟩, N.coordinate_map_coordinate_inverse hx⟩
  · simp [axialTransition, hx, hxA]

private theorem axialTransition_eq_one_on_positive_side
    {A B : Set M} (hdisj : Disjoint A B)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφ : ∀ s, L ≤ s → φ s = 1) {x : M} (hxB : x ∈ B)
    (hxK : x ∉ N.coordinate_map '' (univ ×ˢ Icc (-L) L)) :
    N.axialTransition A φ x = 1 := by
  by_cases hx : x ∈ N.carrier
  · rw [N.axialTransition_eq_of_mem A φ hx]
    apply hφ
    have hs : 0 ≤ (N.coordinate_inverse x).2 := by
      by_contra hn
      exact Set.disjoint_left.mp hdisj
        (hneg ⟨hx, (N.coordinate_inverse_mem x hx).2.1, lt_of_not_ge hn⟩) hxB
    by_contra hn
    apply hxK
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, by linarith,
      (lt_of_not_ge hn).le⟩, N.coordinate_map_coordinate_inverse hx⟩
  · have hxA : x ∉ A := fun h => Set.disjoint_left.mp hdisj h hxB
    simp [axialTransition, hx, hxA]



theorem contMDiff_axialTransition
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hs : ContDiff ℝ ∞ φ) (hzero : ∀ s ≤ -L, φ s = 0)
    (hone : ∀ s, L ≤ s → φ s = 1) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N.axialTransition A φ) := by
  intro x
  by_cases hx : x ∈ N.carrier
  · have haxis := contMDiff_snd.contMDiffAt.comp x
      (N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hx))
    apply (hs.contMDiff.contMDiffAt.comp x haxis).congr_of_eventuallyEq
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.axialTransition_eq_of_mem A φ hy
  · have hK := N.isCompact_coordinate_slab (by linarith : -N.epsilon⁻¹ < -L) hLe
    have hxK := N.not_mem_coordinate_slab_of_not_mem_carrier hLe hx
    have hxside : x ∈ A ∪ B := by
      rw [hcover]
      exact fun hs => hx (N.central_sphere_subset_carrier hs)
    rcases hxside with hxA | hxB
    · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hA.mem_nhds hxA, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hyA hyK
      exact N.axialTransition_eq_zero_on_negative_side hdisj hpos hL hzero hyA hyK
    · apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hxB, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hyB hyK
      exact N.axialTransition_eq_one_on_positive_side hdisj hneg hL hone hyB hyK

theorem axialTransition_mem_Icc {A : Set M} {φ : ℝ → ℝ}
    (hφ : ∀ s, φ s ∈ Icc 0 1) (x : M) : N.axialTransition A φ x ∈ Icc 0 1 := by
  unfold axialTransition
  split_ifs <;> simp_all



theorem hasCompactSupport_one_sub_axialTransition
    {A B : Set M} (hAc : IsCompact (closure A))
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hone : ∀ s, L ≤ s → φ s = 1) :
    HasCompactSupport (fun x => 1 - N.axialTransition A φ x) := by
  let K := N.coordinate_map '' (univ ×ˢ Icc (-L) L)
  have hK : IsCompact K := N.isCompact_coordinate_slab (by linarith) hLe
  apply HasCompactSupport.of_support_subset_isCompact (hAc.union hK)
  intro x hx
  by_contra hn
  have hxA : x ∉ A := fun h => hn (Or.inl (subset_closure h))
  have hxK : x ∉ K := fun h => hn (Or.inr h)
  have hxS : x ∉ N.central_sphere := by
    intro hs
    obtain ⟨hc, hz⟩ := (N.mem_central_sphere_iff x).mp hs
    apply hxK
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, by simpa [hz] using hL.le,
      by simpa [hz] using hL.le⟩, N.coordinate_map_coordinate_inverse hc⟩
  have hxB : x ∈ B := by
    have hc : x ∈ A ∪ B := by rwa [hcover]
    exact hc.resolve_left hxA
  have heq := N.axialTransition_eq_one_on_positive_side hdisj hneg hL hone hxB hxK
  exact hx (by simp only [heq, sub_self])



theorem hasCompactSupport_axialTransition
    {A B : Set M} (hBc : IsCompact (closure B))
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hzero : ∀ s ≤ -L, φ s = 0) : HasCompactSupport (N.axialTransition A φ) := by
  let K := N.coordinate_map '' (univ ×ˢ Icc (-L) L)
  have hK : IsCompact K := N.isCompact_coordinate_slab (by linarith) hLe
  apply HasCompactSupport.of_support_subset_isCompact (hBc.union hK)
  intro x hx
  by_contra hn
  have hxB : x ∉ B := fun h => hn (Or.inl (subset_closure h))
  have hxK : x ∉ K := fun h => hn (Or.inr h)
  have hxS : x ∉ N.central_sphere := by
    intro hs
    obtain ⟨hc, hz⟩ := (N.mem_central_sphere_iff x).mp hs
    apply hxK
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, by simpa [hz] using hL.le,
      by simpa [hz] using hL.le⟩, N.coordinate_map_coordinate_inverse hc⟩
  have hxA : x ∈ A := by
    have hc : x ∈ A ∪ B := by rwa [hcover]
    exact hc.resolve_right hxB
  exact hx (N.axialTransition_eq_zero_on_negative_side hdisj hpos hL hzero hxA hxK)


theorem gradient_axialTransition (D : LeviCivitaData g) (A : Set M)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : M} (hx : x ∈ N.carrier) :
    D.gradient (N.axialTransition A φ) x =
      deriv φ (N.coordinate_inverse x).2 •
        D.gradient (fun y => (N.coordinate_inverse y).2) x := by
  have he : N.axialTransition A φ =ᶠ[𝓝 x] N.axialCutoff φ := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    rw [N.axialTransition_eq_of_mem A φ hy, N.axialCutoff_eq_of_mem φ hy]
  have hg : D.gradient (N.axialTransition A φ) x = D.gradient (N.axialCutoff φ) x := by
    unfold LeviCivitaData.gradient mvfderiv
    rw [he.mfderiv_eq, he.eq_of_nhds]
  rw [hg, N.gradient_axialCutoff D hφ hx]



theorem axialTransition_eventually_constant_of_not_mem
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hzero : ∀ s ≤ -L, φ s = 0) (hone : ∀ s, L ≤ s → φ s = 1)
    {x : M} (hx : x ∉ N.carrier) :
    ∃ c : ℝ, N.axialTransition A φ =ᶠ[𝓝 x] fun _ => c := by
  have hK := N.isCompact_coordinate_slab (by linarith : -N.epsilon⁻¹ < -L) hLe
  have hxK := N.not_mem_coordinate_slab_of_not_mem_carrier hLe hx
  have hxside : x ∈ A ∪ B := by
    rw [hcover]
    exact fun hs => hx (N.central_sphere_subset_carrier hs)
  rcases hxside with hxA | hxB
  · refine ⟨0, ?_⟩
    filter_upwards [hA.mem_nhds hxA, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hyA hyK
    exact N.axialTransition_eq_zero_on_negative_side hdisj hpos hL hzero hyA hyK
  · refine ⟨1, ?_⟩
    filter_upwards [hB.mem_nhds hxB, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hyB hyK
    exact N.axialTransition_eq_one_on_positive_side hdisj hneg hL hone hyB hyK



theorem gradient_axialTransition_eq_zero_of_not_mem (D : LeviCivitaData g)
    {A B : Set M} (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hzero : ∀ s ≤ -L, φ s = 0) (hone : ∀ s, L ≤ s → φ s = 1)
    {x : M} (hx : x ∉ N.carrier) : D.gradient (N.axialTransition A φ) x = 0 := by
  obtain ⟨c, he⟩ := N.axialTransition_eventually_constant_of_not_mem
    hA hB hdisj hcover hneg hpos hL hLe hzero hone hx
  unfold LeviCivitaData.gradient mvfderiv
  rw [he.mfderiv_eq, he.eq_of_nhds]
  simp



theorem hasCompactSupport_axialTransition_sub
    (N₂ : EpsilonNeck g) {A₁ A₂ : Set M} {φ₁ φ₂ : ℝ → ℝ}
    (hc₁ : HasCompactSupport (fun x => 1 - N.axialTransition A₁ φ₁ x))
    (hc₂ : HasCompactSupport (fun x => 1 - N₂.axialTransition A₂ φ₂ x)) :
    HasCompactSupport (fun x => N.axialTransition A₁ φ₁ x -
      N₂.axialTransition A₂ φ₂ x) := by
  have heq : (fun x => N.axialTransition A₁ φ₁ x -
      N₂.axialTransition A₂ φ₂ x) =
      (fun x => (1 - N₂.axialTransition A₂ φ₂ x) -
        (1 - N.axialTransition A₁ φ₁ x)) := by
    funext x
    ring
  rw [heq]
  exact hc₂.sub hc₁



theorem axialTransition_sub_nonneg
    (N₂ : EpsilonNeck g) {A₁ A₂ : Set M} {φ₁ φ₂ : ℝ → ℝ}
    (hφ₁ : ∀ s, φ₁ s ∈ Icc 0 1) (hφ₂ : ∀ s, φ₂ s ∈ Icc 0 1)
    (hdisj : Disjoint N.carrier N₂.carrier)
    (hinner : N.carrier ⊆ A₂) (houter : Disjoint A₁ N₂.carrier)
    (hnest : A₁ ⊆ A₂) (x : M) :
    0 ≤ N.axialTransition A₁ φ₁ x - N₂.axialTransition A₂ φ₂ x := by
  by_cases hx₁ : x ∈ N.carrier
  · have hx₂ : x ∉ N₂.carrier := fun h => Set.disjoint_left.mp hdisj hx₁ h
    have hzero : N₂.axialTransition A₂ φ₂ x = 0 := by
      simp [axialTransition, hx₂, hinner hx₁]
    rw [hzero, sub_zero]
    exact (N.axialTransition_mem_Icc hφ₁ x).1
  · by_cases hx₂ : x ∈ N₂.carrier
    · have hxA : x ∉ A₁ := fun h => Set.disjoint_left.mp houter h hx₂
      have hone : N.axialTransition A₁ φ₁ x = 1 := by
        simp [axialTransition, hx₁, hxA]
      rw [hone]
      exact sub_nonneg.mpr (N₂.axialTransition_mem_Icc hφ₂ x).2
    · by_cases hxA₁ : x ∈ A₁
      · simp [axialTransition, hx₁, hx₂, hxA₁, hnest hxA₁]
      · have hle := (N₂.axialTransition_mem_Icc (A := A₂) hφ₂ x).2
        simpa [axialTransition, hx₁, hxA₁] using sub_nonneg.mpr hle

end PoincareConjecture.EpsilonNeck
