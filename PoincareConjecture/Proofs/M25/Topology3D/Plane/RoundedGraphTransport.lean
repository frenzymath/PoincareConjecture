import PoincareConjecture.Proofs.M25.Topology3D.Plane.GraphTransport
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothHeight
import PoincareConjecture.Proofs.M25.Topology3D.Plane.NormalGraph
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_smooth_graph_ambient_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L U w a b : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L U ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hab : a ≤ b) (ha : L < a) (hb : b < U)
    (h : Icc a b × sphere (0 : E) 1 → ℝ) (hh : Continuous h)
    (hbound : ∀ p, |h p| < w) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ A < w ∧ ∃ g : ℝ × sphere (0 : E) 1 → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ p, |g p| < A) ∧
      (∀ z : Icc a b, ∀ q : sphere (0 : E) 1, |g (z, q) - h (z, q)| < ε) ∧
      ∃ F : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
        (∃ K : Set E, IsCompact K ∧
          ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
        (∀ z, HasCompactSupport (fun x => F z x - x) ∧
          HasCompactSupport (fun x => (F z).symm x - x)) ∧
        (∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
          F z (c z q) = c z q + g (z, q) •
            curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
          (fun p : ℝ × sphere (0 : E) 1 => F p.1 (c p.1 p.2)) ∧
        (∀ z ∈ Icc a b, Injective (fun q => F z (c z q)) ∧
          ∀ q : sphere (0 : E) 1,
            Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun p => F z (c z p)) q)) ∧
        ∀ z : Icc a b, ∀ q : sphere (0 : E) 1,
          dist (F z (c z q)) (c z q + h (z, q) •
            curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) < ε := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  obtain ⟨p0, _, hp0⟩ :=
    (isCompact_univ : IsCompact (univ : Set (Icc a b × sphere (0 : E) 1))).exists_isMaxOn
      ⟨(⟨a, ⟨le_rfl, hab⟩⟩, q0), mem_univ _⟩ hh.abs.continuousOn
  let A := (|h p0| + w) / 2
  have hA : 0 < A := by
    dsimp [A]
    linarith [abs_nonneg (h p0), hbound p0]
  have hAw : A < w := by
    dsimp [A]
    linarith [hbound p0]
  have hhA (p : Icc a b × sphere (0 : E) 1) : |h p| < A := by
    have hm : |h p| ≤ |h p0| := hp0 (mem_univ p)
    dsimp [A]
    linarith [hbound p0]
  obtain ⟨g, hg, hgbound, herror⟩ :=
    exists_smooth_bounded_family_height hab h hh hhA hε
  obtain ⟨F, hFsmooth, hInvsmooth, hK, hcompact, hFgraph⟩ :=
    exists_curveAnnularTube_graph_transport o q0 c T hw hs he hfwd hInv ha hb hAw g hg hgbound
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => F p.1 (c p.1 p.2)) :=
    hFsmooth.contMDiff.comp (contMDiff_fst.prodMk_space hc)
  have hnormal := curveAnnularTube_smooth_normal_graph o q0 c T hw hs he hfwd hInv
    g hg (fun z _ q => (hgbound (z, q)).trans hAw)
  refine ⟨A, hA, hAw, g, hg, hgbound, herror, F, hFsmooth, hInvsmooth, hK,
    hcompact, hFgraph, hG, ?_, ?_⟩
  · intro z hz
    have hzI : z ∈ Ioo L U := ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
    have hfun : (fun q => F z (c z q)) = (fun q : sphere (0 : E) 1 =>
        c z q + g (z, q) • curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) :=
      funext (hFgraph z hz)
    rw [hfun]
    exact hnormal.2 z hzI
  · intro z q
    have hN : ‖curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))‖ ≤ 1 := by
      by_cases hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) = 0
      · simp only [curveFamilyNormal, hv, norm_zero, inv_zero, map_zero, smul_zero]
        norm_num
      · exact (norm_curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) hv).le
    calc
      dist (F z (c z q)) (c z q + h (z, q) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) =
          ‖(g (z, q) - h (z, q)) •
            curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))‖ := by
        rw [hFgraph z z.2 q, dist_eq_norm]
        congr 1
        rw [sub_smul]
        abel
      _ = |g (z, q) - h (z, q)| *
          ‖curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |g (z, q) - h (z, q)| := mul_le_of_le_one_right (abs_nonneg _) hN
      _ < ε := herror z q

end PoincareConjecture.M25.Topology3D
