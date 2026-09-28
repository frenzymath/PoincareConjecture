import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_radialStereo_transport_isotopy (v : E) (hv : ‖v‖ = 1)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, (ℝ ∙ v)ᗮ × ℝ) 𝓘(ℝ, (ℝ ∙ v)ᗮ × ℝ)
      ((ℝ ∙ v)ᗮ × ℝ) ((ℝ ∙ v)ᗮ × ℝ) ∞)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × ((ℝ ∙ v)ᗮ × ℝ) => Φ p.1 p.2))
    (hzero : ∀ p, Φ 0 p = p) (hsnd : ∀ t p, (Φ t p).2 = p.2)
    {C : Set ((ℝ ∙ v)ᗮ × ℝ)} (hC : IsCompact C) (hCs : C ⊆ univ ×ˢ Ioi 0)
    (hfix : ∀ t p, p ∉ C → Φ t p = p) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧ (∀ t y, ‖Ψ t y‖ = ‖y‖) ∧
      (∀ t w, Ψ t (stereoInvFun hv w : E) =
        (stereoInvFun hv ((Φ t (w, 1)).1) : E)) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ radialStereoTarget v ∧
        ∀ t y, y ∉ K → Ψ t y = y := by
  let e := radialStereoChart v hv
  obtain ⟨Ψ, hΨ, hΨzero, htrack, hΨfix, hcompact, htarget⟩ :=
    exists_chart_transport_isotopy e (radialStereoChart_contDiffOn v hv)
      (radialStereoChart_symm_contDiffOn v hv) Φ hΦ hzero hC hCs hfix
  refine ⟨Ψ, hΨ, hΨzero, ?_, ?_, e '' C, hcompact, htarget, hΨfix⟩
  · intro t y
    by_cases hy : y ∈ e.target
    · let p := e.symm y
      have hps : p ∈ e.source := e.map_target hy
      have hpeq : e p = y := e.right_inv hy
      rw [← hpeq, htrack t p hps]
      have hpos : 0 < (Φ t p).2 := by rw [hsnd]; exact hps.2
      change ‖radialStereoMap v hv (Φ t p)‖ = ‖radialStereoMap v hv p‖
      rw [radialStereoMap_norm v hv _ hpos, radialStereoMap_norm v hv p hps.2, hsnd]
    · rw [hΨfix t y (fun h => hy (htarget h))]
  · intro t w
    have hp : (w, (1 : ℝ)) ∈ e.source :=
      ⟨mem_univ _, (zero_lt_one : (0 : ℝ) < 1)⟩
    have h := htrack t (w, 1) hp
    change Ψ t (radialStereoMap v hv (w, 1)) =
      radialStereoMap v hv (Φ t (w, 1)) at h
    simpa only [radialStereoMap, hsnd, one_smul] using h

end PoincareConjecture.M25.Topology3D
