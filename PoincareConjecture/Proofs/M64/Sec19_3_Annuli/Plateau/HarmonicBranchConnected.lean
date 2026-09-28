import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HarmonicBranchFinite
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen














set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem interior_eq_empty_of_zero_alternative
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {S : Set X} (hproper : S ≠ univ)
    (hlocal : ∀ x : X, S ∈ 𝓝 x ∨ ∀ᶠ y in 𝓝[≠] x, y ∉ S) :
    interior S = ∅ := by
  have hclosed : IsClosed (interior S) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : S ∉ 𝓝 x := by
      simpa only [mem_compl_iff, mem_interior_iff_mem_nhds] using hx
    have hi := (hlocal x).resolve_left hx'
    rw [eventually_nhdsWithin_iff] at hi
    filter_upwards [hi] with y hy
    change y ∉ interior S
    intro hyS
    by_cases hyx : y = x
    · exact hx (hyx ▸ hyS)
    · exact hy hyx (interior_subset hyS)
  rcases isClopen_iff.mp ⟨hclosed, isOpen_interior⟩ with h | h
  · exact h
  · exact False.elim (hproper (univ_subset_iff.mp (h ▸ interior_subset)))

section Harmonic

variable {n : ℕ}
  {Γ : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
  {u : ℂ → EuclideanSpace ℝ (Fin n)} {O : Set ℂ}
  (hO : IsOpen O) (hconnected : IsPreconnected O)
  (hu : ContDiffOn ℝ 2 u O)
  (hΓ : ∀ z ∈ O, ContDiffAt ℝ 1 Γ (u z))
  (hsym : ∀ z ∈ O, ∀ a b : EuclideanSpace ℝ (Fin n),
    Γ (u z) a b = Γ (u z) b a)
  (hτ : ∀ z ∈ O,
    ConnectionVariation.covDerivAlong Γ u
        (fun w => fderiv ℝ u w 1) 1 z +
      ConnectionVariation.covDerivAlong Γ u
        (fun w => fderiv ℝ u w Complex.I) Complex.I z = 0)
  (hnonconstant : ∃ x ∈ O, ∃ y ∈ O, u x ≠ u y)

include hO hconnected hu hΓ hsym hτ hnonconstant





theorem m64PlaneHarmonicDifferential_zeroSet_not_mem_nhds
    {z : ℂ} (hz : z ∈ O) :
    m64PlaneDifferentialZeroSet u ∉ 𝓝 z := by
  let : PreconnectedSpace O := isPreconnected_iff_preconnectedSpace.mp hconnected
  let Z : Set O := {x | fderiv ℝ u x = 0}
  have hproper : Z ≠ univ := by
    intro hfull
    have hd : EqOn (fderiv ℝ u) 0 O := by
      intro x hx
      exact (show (⟨x, hx⟩ : O) ∈ Z from hfull ▸ mem_univ _)
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonconstant
    exact hxy (hO.is_const_of_fderiv_eq_zero hconnected
      (hu.differentiableOn (by norm_num)) hd hx hy)
  have hlocal (x : O) : Z ∈ 𝓝 x ∨ ∀ᶠ y in 𝓝[≠] x, y ∉ Z := by
    have hc : ContinuousAt (fun y : O => (y : ℂ)) x :=
      continuous_subtype_val.continuousAt
    rcases M60.harmonic_differential_eventually_zero_or_isolated
        hO hu hΓ hsym hτ x.property with hall | hisol
    · left
      exact hc.eventually hall
    · right
      rw [eventually_nhdsWithin_iff] at hisol ⊢
      filter_upwards [hc.eventually hisol] with y hy
      intro hyx hyZ
      exact hy (fun h => hyx (Subtype.ext h)) hyZ
  have hempty := interior_eq_empty_of_zero_alternative hproper hlocal
  intro hzero
  have hc : ContinuousAt (fun x : O => (x : ℂ)) ⟨z, hz⟩ :=
    continuous_subtype_val.continuousAt
  have hsub : Z ∈ 𝓝 (⟨z, hz⟩ : O) :=
    hc.eventually hzero
  have hmem := mem_interior_iff_mem_nhds.mpr hsub
  rw [hempty] at hmem
  exact hmem



theorem m64PlaneHarmonicDifferential_eventually_ne_zero
    {z : ℂ} (hz : z ∈ O) :
    ∀ᶠ w in 𝓝[≠] z, fderiv ℝ u w ≠ 0 := by
  exact (M60.harmonic_differential_eventually_zero_or_isolated
    hO hu hΓ hsym hτ hz).resolve_left
      (m64PlaneHarmonicDifferential_zeroSet_not_mem_nhds
        hO hconnected hu hΓ hsym hτ hnonconstant hz)





theorem m64PlaneHarmonicDifferential_zeroSet_finite_on_compact
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    (m64PlaneDifferentialZeroSet u ∩ K).Finite := by
  have hD : ContinuousOn (fderiv ℝ u) K :=
    (hu.continuousOn_fderiv_of_isOpen hO (by norm_num)).mono hKO
  have hclosed : IsClosed (m64PlaneDifferentialZeroSet u ∩ K) := by
    rw [inter_comm]
    exact hD.preimage_isClosed_of_isClosed hK.isClosed (isClosed_singleton (x := 0))
  exact m64PlaneHarmonicDifferential_zeroSet_finite hO hu hΓ hsym hτ
    (hK.of_isClosed_subset hclosed inter_subset_right) hKO
    (fun z hz => m64PlaneHarmonicDifferential_zeroSet_not_mem_nhds
      hO hconnected hu hΓ hsym hτ hnonconstant (hKO hz.2))

end Harmonic

end PoincareConjecture
