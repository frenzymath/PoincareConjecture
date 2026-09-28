import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryNoncritical
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPotentialUniqueness













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => Set.preimage (fun p : Plane => p 0) (Ioi (0 : ℝ))

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)








theorem annular_harmonic_noncritical_boundary
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (x : closure scalarAnnulus) (hxnorm : ‖(x : Plane)‖ = 1 ∨ ‖(x : Plane)‖ = 2) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (O : Set Plane)
      (J : Plane → Plane →L[ℝ] ℝ),
      (x : Plane) ∈ e.target ∧ e.symm x ∈ closure O ∧ IsOpen O ∧ Convex ℝ O ∧
      IsCompact (closure O) ∧ closure O ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
      (∃ r : ℝ, 0 < r ∧ O = Metric.ball (e.symm (x : Plane)) r ∩ Half) ∧
      ContinuousOn J e.source ∧ EqOn (fderiv ℝ (H ∘ e)) J O ∧
      (∀ z ∈ closure O, HasFDerivWithinAt (H ∘ e) (J z) (closure O) z) ∧
      J (e.symm x) ≠ 0 := by
  obtain ⟨K, hKc, hKs, hKlap, hKinner, hKouter, hboundary⟩ :=
    exists_annular_harmonic_potential_noncritical_boundary D
  have hHK : EqOn H K {p : Plane | 0 ≤ scalarAnnulusDefining p} := by
    apply annular_harmonic_eq_on_closed D hHc hKc hHs hKs hlap hKlap
    intro p hp
    rcases (scalarAnnulusDefining_zero p).mp hp with hp | hp
    · rw [hinner p hp, hKinner p hp]
    · rw [houter p hp, hKouter p hp]
  have hclosed : closure scalarAnnulus ⊆ {p : Plane | 0 ≤ scalarAnnulusDefining p} :=
    closure_minimal (fun p hp => ((scalarAnnulusDefining_pos p).mpr hp).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  obtain ⟨e, O, J, hx, hxO, hO, hconv, hOc, hOs, he, hei, hflat, hshape,
    hJc, hJeq, hJderiv, hJne⟩ := hboundary x hxnorm
  have hOH : O ⊆ Half := by
    obtain ⟨r, -, hr⟩ := hshape
    rw [hr]
    exact inter_subset_right
  have heO : e '' O ⊆ scalarAnnulus := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hflat z (hOs (subset_closure hz))).mpr (hOH hz)
  have hcomp : EqOn (H ∘ e) (K ∘ e) (closure O) := by
    intro z hz
    have hec := e.continuousOn.continuousAt (e.open_source.mem_nhds (hOs hz))
    exact hHK (hclosed (closure_mono heO (mem_closure_image hec hz)))
  refine ⟨e, O, J, hx, hxO, hO, hconv, hOc, hOs, he, hei, hflat,
    hshape, hJc, ?_, ?_, hJne⟩
  · intro z hz
    have hloc : H ∘ e =ᶠ[𝓝 z] K ∘ e := by
      filter_upwards [hO.mem_nhds hz] with y hy
      exact hcomp (subset_closure hy)
    exact hloc.fderiv_eq.trans (hJeq hz)
  · intro z hz
    exact (hJderiv z hz).congr (fun y hy => hcomp hy) (hcomp hz)

end PoincareConjecture.M64Uniformization
