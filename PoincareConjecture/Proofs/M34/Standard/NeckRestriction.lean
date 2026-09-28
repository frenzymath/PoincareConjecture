import PoincareConjecture.Definitions.Ch12.StandardCap










set_option autoImplicit false

namespace PoincareConjecture



theorem RoundCylinderFamilyClose.mono_time
    {epsilon : ℝ} {I J : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (h : RoundCylinderFamilyClose epsilon I B) (hJI : J ⊆ I) :
    RoundCylinderFamilyClose epsilon J B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  exact ⟨fun u hu => hsmooth u (hJI hu), bound, hbound,
    fun u hu => hjet u (hJI hu)⟩



theorem RoundCylinderFamilyClose.at_time
    {epsilon : ℝ} {I : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (h : RoundCylinderFamilyClose epsilon I B) {u : ℝ} (hu : u ∈ I) :
    RoundCylinderClose epsilon u (B u) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  exact ⟨hsmooth u hu, bound, hbound, hjet u hu⟩



theorem roundCylinderFamilyClose_singleton_iff
    {epsilon u : ℝ} {B : ℝ → RoundCylinderTwoTensor} :
    RoundCylinderFamilyClose epsilon {u} B ↔
      RoundCylinderClose epsilon u (B u) := by
  constructor
  · intro h
    exact h.at_time (Set.mem_singleton u)
  · rintro ⟨hsmooth, bound, hbound, hjet⟩
    refine ⟨?_, bound, hbound, ?_⟩
    · intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact hsmooth
    · intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact hjet



theorem StandardSpacetimeCylinderClose.mono_time
    {A : StandardCylinderAtlas} {g : ℝ → RiemannianMetric 3 StandardCapSpace}
    {epsilon origin scale : ℝ} {I J : Set ℝ} {x : StandardCapSpace}
    {N : StandardCylinderPatch epsilon⁻¹ x}
    (h : StandardSpacetimeCylinderClose A g epsilon origin scale I N)
    (hJI : J ⊆ I) :
    StandardSpacetimeCylinderClose A g epsilon origin scale J N :=
  RoundCylinderFamilyClose.mono_time h hJI



def StandardEvolvingNeck.restrict
    {A : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon : ℝ} {x : StandardCapSpace}
    {I J : Set ℝ} (N : StandardEvolvingNeck A F t epsilon x I)
    (hJI : J ⊆ I) : StandardEvolvingNeck A F t epsilon x J where
  time_mem := N.time_mem
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scalar_pos := N.scalar_pos
  patch := N.patch
  interval_survival := fun u hu => N.interval_survival u (hJI hu)
  close := N.close.mono_time hJI



def StandardFlowAsymptoticCertificate.restrict
    {A : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {epsilon t₀ t₁ : ℝ}
    (C : StandardFlowAsymptoticCertificate A F epsilon t₀)
    (h₁ : 0 ≤ t₁) (h₁₀ : t₁ ≤ t₀) :
    StandardFlowAsymptoticCertificate A F epsilon t₁ where
  epsilon_pos := C.epsilon_pos
  t₀_mem := ⟨h₁, lt_of_le_of_lt h₁₀ C.t₀_mem.2⟩
  compact_set := C.compact_set
  compact := C.compact
  patches := by
    intro x hx
    obtain ⟨N, hN⟩ := C.patches x hx
    exact ⟨N, hN.mono_time (fun _ hu => ⟨hu.1, hu.2.trans h₁₀⟩)⟩

end PoincareConjecture
