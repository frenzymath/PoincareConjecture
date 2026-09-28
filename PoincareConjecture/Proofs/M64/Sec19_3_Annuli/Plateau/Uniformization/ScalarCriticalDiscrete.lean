import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCriticalLocal
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem scalarPotential_nonconstant_of_boundary_values {H : Plane → ℝ}
    (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ¬ ∃ c : ℝ, EqOn H (fun _ => c) scalarAnnulus := by
  rintro ⟨c, hc⟩
  have hsurj := scalarPotential_surjOn_interval hHc hinner houter
  obtain ⟨x, hx, hxval⟩ := hsurj (by norm_num : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1)
  obtain ⟨y, hy, hyval⟩ := hsurj (by norm_num : (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1)
  have hxconst := hc hx
  have hyconst := hc hy
  dsimp only at hxconst hyconst
  linarith

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarPotential_critical_isolated {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {p : Plane} (hp : p ∈ scalarAnnulus) :
    ∀ᶠ y in 𝓝[≠] p, fderiv ℝ H y ≠ 0 := by
  let C : Set scalarAnnulus := {x | ∀ᶠ y in 𝓝 (x : Plane), fderiv ℝ H y = 0}
  let : PreconnectedSpace scalarAnnulus :=
    Subtype.preconnectedSpace scalarAnnulus_isConnected.isPreconnected
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hx' : ∀ᶠ y in 𝓝 (x : Plane), fderiv ℝ H y = 0 := hx
    exact continuousAt_subtype_val.eventually hx'.eventually_nhds
  have hCclosed : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hnot : ¬ ∀ᶠ y in 𝓝 (x : Plane), fderiv ℝ H y = 0 := hx
    have halternative := scalarPotential_local_critical_alternative D hHs hlap x.property
    have hlocal := halternative.resolve_left hnot
    rw [eventually_nhdsWithin_iff] at hlocal
    filter_upwards [continuousAt_subtype_val.eventually hlocal] with y hy
    intro hyC
    have hyzero : ∀ᶠ z in 𝓝 (y : Plane), fderiv ℝ H z = 0 := hyC
    by_cases heq : y = x
    · exact hx (heq ▸ hyC)
    · have hne : (y : Plane) ≠ (x : Plane) := fun h => heq (Subtype.ext h)
      exact hy hne hyzero.self_of_nhds
  have hCempty : C = ∅ := by
    apply (isClopen_iff.mp ⟨hCclosed, hCopen⟩).resolve_right
    intro hfull
    have hzero : EqOn (fderiv ℝ H) 0 scalarAnnulus := by
      intro x hx
      have hc : (⟨x, hx⟩ : scalarAnnulus) ∈ C := by rw [hfull]; exact mem_univ _
      have hc' : ∀ᶠ y in 𝓝 x, fderiv ℝ H y = 0 := hc
      exact hc'.self_of_nhds
    have hdiff := (contMDiffOn_iff_contDiffOn.mp hHs).differentiableOn (by simp)
    exact scalarPotential_nonconstant_of_boundary_values hHc hinner houter
      (scalarAnnulus_isOpen.exists_is_const_of_fderiv_eq_zero
        scalarAnnulus_isConnected.isPreconnected hdiff hzero)
  apply (scalarPotential_local_critical_alternative D hHs hlap hp).resolve_left
  intro hlocal
  have hc : (⟨p, hp⟩ : scalarAnnulus) ∈ C := hlocal
  rw [hCempty] at hc
  exact hc

theorem scalarPotential_critical_finite_on_compact {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {K : Set Plane} (hK : IsCompact K) (hKsub : K ⊆ scalarAnnulus) :
    (K ∩ {x | fderiv ℝ H x = 0}).Finite := by
  by_contra hinfinite
  have hinf : (K ∩ {x | fderiv ℝ H x = 0}).Infinite := hinfinite
  obtain ⟨p, hp, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK inter_subset_left
  have hi := scalarPotential_critical_isolated D hHc hHs hlap hinner houter (hKsub hp)
  exact (accPt_iff_frequently_nhdsNE.mp hacc) (hi.mono fun y hy h => hy h.2)

theorem scalarPotential_critical_finite_on_levels {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1) :
    ((scalarAnnulus ∩ H ⁻¹' K) ∩ {x | fderiv ℝ H x = 0}).Finite :=
  scalarPotential_critical_finite_on_compact D hHc hHs hlap hinner houter
    (scalarPotential_compact_levels hHc hinner houter hK hKsub) inter_subset_left

end PoincareConjecture.M64Uniformization
