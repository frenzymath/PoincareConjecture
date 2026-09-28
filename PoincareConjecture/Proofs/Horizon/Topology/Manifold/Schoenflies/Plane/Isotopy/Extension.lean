import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Tube.Tube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Compact












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]



theorem exists_ambient_isotopy_of_smooth_circle_family
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    {a b : ℝ} (hab : a ≤ b)
    (hi : ∀ t ∈ Icc a b, Injective (c t))
    (hm : ∀ t ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c t) q)) :
    ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Phi p.1 p.2) ∧
      (∃ S : Set E, IsCompact S ∧ ∀ t x, x ∉ S → Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ q : sphere (0 : E) 1, Phi t (c a q) = c t q := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  obtain ⟨m, hm0, w, hw0, _, T, hs, he, hT, hInv⟩ :=
    exists_curveAnnularTube o q0 c hc hab hi hm
  have hsource : Icc a b ×ˢ sphere (0 : E) 1 ⊆ T.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [hs]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    change |‖x‖ - 1| < w
    rw [show ‖x‖ = 1 from norm_eq_of_mem_sphere ⟨x, hx⟩]
    simpa using hw0
  obtain ⟨G, V, hG, _, hKV, _, hEq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact
      (isCompact_Icc.prod (isCompact_sphere (0 : E) 1)) T.open_source hsource
      (fun p : ℝ × E => (T p).2) hT.snd
  have hGc (t : ℝ) (ht : t ∈ Icc a b) (q : sphere (0 : E) 1) :
      G (t, (q : E)) = c t q := by
    rw [hEq (hKV ⟨ht, q.property⟩)]
    change (T (t, (q : E))).2 = c t q
    rw [he]
    exact curveAnnularExtension_apply_sphere o q0 c t q
  have hagree : ∀ t ∈ Icc a b, ∀ x ∈ sphere (0 : E) 1,
      T (t, x) = (t, G (t, x)) := by
    intro t ht x hx
    rw [he, hGc t ht ⟨x, hx⟩, curveAnnularExtension_apply_sphere o q0 c t ⟨x, hx⟩]
  obtain ⟨Phi, hPhi0, hPhis, hPhic, hPhicomp⟩ :=
    exists_ambient_isotopy_of_compact_isotopy (isCompact_sphere (0 : E) 1)
      G hG T hsource hInv.contMDiffOn hagree
  refine ⟨Phi, hPhi0, hPhis, hPhic, ?_⟩
  intro t ht q
  simpa only [hGc a ⟨le_rfl, hab⟩ q, hGc t ht q] using
    hPhicomp t ht (q : E) q.property

end Poincare.Manifold.Schoenflies.Plane
