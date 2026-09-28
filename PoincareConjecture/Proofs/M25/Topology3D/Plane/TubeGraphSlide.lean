import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedRadialSlide
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CompactConjugation
import PoincareConjecture.Proofs.M25.Topology3D.Plane.AnnularExtension

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_curveAnnularTube_bump_slide
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L U w : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L U ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 1)
    (a d : ℝ × E → ℝ) (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ d)
    {A B r l u : ℝ} (hderiv : ∀ x, |deriv β x| ≤ B)
    (hsmall : ∀ v, B * |d v| < 1) (hcenter : ∀ v, |a v| ≤ A)
    (hsupport : ∀ x, r ≤ |x| → β x = 0) (hr : 0 < r) (hwidth : A + r < w)
    (hl : L < l) (hu : u < U) (htime : ∀ v : ℝ × E, v.1 ∉ Icc l u → d v = 0) :
    ∃ Ψ : (ℝ × E) ≃ₘ[ℝ] (ℝ × E),
      (∀ p, (Ψ p).1 = p.1 ∧ (Ψ.symm p).1 = p.1) ∧
      HasCompactSupport (fun p => Ψ p - p) ∧
      HasCompactSupport (fun p => Ψ.symm p - p) ∧
      (∀ p, p ∉ T '' (Icc l u ×ˢ {x : E | |‖x‖ - 1| ≤ A + r}) →
        Ψ p = p ∧ Ψ.symm p = p) ∧
      ∀ z ∈ Ioo L U, ∀ q : sphere (0 : E) 1, |a (z, (q : E)) + d (z, (q : E))| < w →
        Ψ (z, c z q + a (z, (q : E)) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) =
        (z, c z q + (a (z, (q : E)) + d (z, (q : E))) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  obtain ⟨R, _, hRtime, hRfix, hRgraph, _, _⟩ :=
    exists_supported_radial_bump_slide β hβ hβ0 a d ha hd hderiv hsmall hcenter
      hsupport hr (hwidth.trans hw) htime
  let K : Set (ℝ × E) := Icc l u ×ˢ {x : E | |‖x‖ - 1| ≤ A + r}
  have hK : IsCompact K := isCompact_time_closedAnnulus l u (A + r)
  have hKs : K ⊆ T.source := by
    intro p hp
    rw [hs]
    exact ⟨⟨hl.trans_le hp.1.1, hp.1.2.trans_lt hu⟩, hp.2.trans_lt hwidth⟩
  have hKfix (p : ℝ × E) (hp : p ∉ K) : R p = p := by
    apply hRfix
    by_cases hz : p.1 ∈ Icc l u
    · right
      have hn : ¬ |‖p.2‖ - 1| ≤ A + r := fun h => hp ⟨hz, h⟩
      exact (lt_of_not_ge hn).le
    · exact Or.inl hz
  obtain ⟨Ψ, hΨ, _, hΨfix, hΨInvfix, hΨsupport, hΨInvsupport⟩ :=
    exists_compact_tube_conjugate T hfwd hInv R hK hKs hKfix
  have hTtime (p : ℝ × E) : (T p).1 = p.1 := by rw [he]
  have hInvtime (p : ℝ × E) (hp : p ∈ T.target) : (T.symm p).1 = p.1 := by
    have h := congrArg Prod.fst (T.right_inv hp)
    rwa [hTtime] at h
  have hΨtime (p : ℝ × E) : (Ψ p).1 = p.1 := by
    by_cases hp : p ∈ T.target
    · rw [hΨ p hp, hTtime, (hRtime _).1, hInvtime p hp]
    · have hn : p ∉ T '' K := by
        rintro ⟨x, hx, rfl⟩
        exact hp (T.map_source (hKs hx))
      rw [hΨfix p hn]
  have hΨInvtime (p : ℝ × E) : (Ψ.symm p).1 = p.1 := by
    simpa only [Ψ.apply_symm_apply] using (hΨtime (Ψ.symm p)).symm
  refine ⟨Ψ, (fun p => ⟨hΨtime p, hΨInvtime p⟩), hΨsupport, hΨInvsupport,
    (fun p hp => ⟨hΨfix p hp, hΨInvfix p hp⟩), ?_⟩
  intro z hz q htarget
  have habound : |a (z, (q : E))| < w := (hcenter _).trans_lt (by linarith)
  have hapos : -1 < a (z, (q : E)) := by linarith [(abs_lt.mp habound).1]
  have hsumpos : -1 < a (z, (q : E)) + d (z, (q : E)) := by
    linarith [(abs_lt.mp htarget).1]
  have hsource : (z, (1 + a (z, (q : E))) • (q : E)) ∈ T.source := by
    rw [hs]
    refine ⟨hz, ?_⟩
    change |‖(1 + a (z, (q : E))) • (q : E)‖ - 1| < w
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + a (z, (q : E))),
      norm_eq_of_mem_sphere q, mul_one, add_sub_cancel_left] using habound
  have hTgraph (t : ℝ) (ht : -1 < t) :
      T (z, (1 + t) • (q : E)) =
        (z, c z q + t • curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) := by
    rw [he, curveAnnularExtension_apply_radial o q0 c z q ht]
  calc
    Ψ (z, c z q + a (z, (q : E)) •
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) =
        Ψ (T (z, (1 + a (z, (q : E))) • (q : E))) :=
      congrArg Ψ (hTgraph _ hapos).symm
    _ = T (R (z, (1 + a (z, (q : E))) • (q : E))) := by
      rw [hΨ _ (T.map_source hsource), T.left_inv hsource]
    _ = T (z, (1 + (a (z, (q : E)) + d (z, (q : E)))) • (q : E)) := by
      simpa only [add_assoc] using congrArg T (hRgraph z (q : E) (norm_eq_of_mem_sphere q))
    _ = _ := hTgraph _ hsumpos

end PoincareConjecture.M25.Topology3D
