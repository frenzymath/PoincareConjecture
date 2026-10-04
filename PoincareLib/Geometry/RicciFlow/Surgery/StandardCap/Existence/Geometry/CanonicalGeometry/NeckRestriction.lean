import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
# Restricting fixed cylinder comparisons

The uniform spatial bounds of Morgan-Tian Definition 2.16 and Remark 2.17,
printed p. 30, restrict to arbitrary smaller time sets. These lemmas keep
the same spatial coordinates and comparison bound in the standard-cap
asymptotics of Proposition 12.7, printed pp. 298-299.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Restrict the common bound to a smaller time set, including empty and
singleton sets (Morgan-Tian Definition 2.16 and Remark 2.17, p. 30). -/
theorem RoundCylinderFamilyClose.mono_time
    {epsilon : ℝ} {I J : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (h : RoundCylinderFamilyClose epsilon I B) (hJI : J ⊆ I) :
    RoundCylinderFamilyClose epsilon J B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  exact ⟨fun u hu => hsmooth u (hJI hu), bound, hbound,
    fun u hu => hjet u (hJI hu)⟩

/-- Evaluate a common cylinder bound at a time in its domain
(Morgan-Tian Definition 2.16 and Remark 2.17, p. 30). -/
theorem RoundCylinderFamilyClose.at_time
    {epsilon : ℝ} {I : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (h : RoundCylinderFamilyClose epsilon I B) {u : ℝ} (hu : u ∈ I) :
    RoundCylinderClose epsilon u (B u) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  exact ⟨hsmooth u hu, bound, hbound, hjet u hu⟩

/-- A singleton-time comparison is the spatial comparison at that model
time (Morgan-Tian Definition 2.16 and Remark 2.17, p. 30). -/
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

/-- Restrict a standard spacetime comparison without changing its clock,
scale or spatial patch (Morgan-Tian Proposition 12.7, pp. 298-299). -/
theorem StandardSpacetimeCylinderClose.mono_time
    {A : StandardCylinderAtlas} {g : ℝ → RiemannianMetric 3 StandardCapSpace}
    {epsilon origin scale : ℝ} {I J : Set ℝ} {x : StandardCapSpace}
    {N : StandardCylinderPatch epsilon⁻¹ x}
    (h : StandardSpacetimeCylinderClose A g epsilon origin scale I N)
    (hJI : J ⊆ I) :
    StandardSpacetimeCylinderClose A g epsilon origin scale J N :=
  RoundCylinderFamilyClose.mono_time h hJI

/-- Restrict the survival interval of a fixed evolving neck, retaining its
literal patch (Morgan-Tian Definition 2.16 and Remark 2.17, p. 30). -/
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

/-- Shortening an asymptotic time slab preserves its compact exceptional
set and fixed patches (Morgan-Tian Proposition 12.7, pp. 298-299). -/
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

end PoincareMT
