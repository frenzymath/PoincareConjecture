import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.MorseMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.MorseSquareSqueeze
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem exists_nested_disk_pair_isotopy_fixing_entire_negative_morse_square
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1)
    (hB : B 1 '' closedBall 0 1 ⊆ B 0 '' ball 0 1)
    {r t w a ρ : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hρ : 0 < ρ) (hρa : ρ < a) (haw : a < w) (hwr : w ≤ hyperbolaRadius r t)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (hAlevel : ∀ x ∈ openSquare r,
      x ∈ (A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hBlevel : ∀ x ∈ openSquare r,
      x ∈ (B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    let P := (fun z : Real × Real =>
      negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1)
    ρ < r ∧ ∃ K : Set E2, IsCompact K ∧ Disjoint K P ∧
      Disjoint K (closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        (∀ i, Φ 1 '' (A i '' sphere 0 1) = B i '' sphere 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧ P ⊆ U ∧ closedSquare ρ ⊆ U ∧
          ∀ u, EqOn (Φ u) id U := by
  have ha : 0 < a := hρ.trans hρa
  obtain ⟨K, hK, hKP, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦmatch, _, V, hV, hPV, hΦV⟩ :=
    Nested.exists_supported_nested_negative_morse_isotopy
      A B hA hB hr ht htr ha haw hwr hedge hAlevel hBlevel
  let P := (fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
    (Icc (-a) a ×ˢ Icc 0 1)
  let W := V ∩ Kᶜ
  have hW : IsOpen W := hV.inter hK.isClosed.isOpen_compl
  have hPW : P ⊆ W := fun x hx => ⟨hPV hx, fun hk => disjoint_left.mp hKP hk hx⟩
  have har : t + a ^ 2 < r ^ 2 := by
    have hlt := haw.trans_le hwr
    have hs := hyperbolaRadius_sq htr.le
    have hp := hyperbolaRadius_pos htr
    nlinarith
  obtain ⟨J, _, hJsq, hJlevel, H, hHfix, hHmiddle, hHsq⟩ :=
    exists_morse_square_squeeze_into_ribbon_neighborhood hr ht hρ hρa har W hW hPW
  have hHP (x : E2) (hx : x ∈ P) : H x = x := by
    obtain ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩ := hx
    apply hHmiddle
    change |(2 * u - 1) * Real.sqrt (t + s ^ 2)| ≤ Real.sqrt (t + s ^ 2)
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hu' : |2 * u - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simpa using mul_le_mul_of_nonneg_right hu' (Real.sqrt_nonneg _)
  have hpreserve (D : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
      (hlevel : ∀ x ∈ openSquare r,
        x ∈ (D 0 '' sphere (0 : E2) 1) ∪ (D 1 '' sphere (0 : E2) 1) →
        -(x 0)^2 + (x 1)^2 = -t) (i : Fin 2) :
      H '' (D i '' closedBall 0 1) = D i '' closedBall 0 1 := by
    have hfix : ∀ x ∈ D i '' sphere (0 : E2) 1, H x = x := by
      intro x hx
      apply hHfix
      intro hxJ
      apply disjoint_left.mp hJlevel hxJ
      apply hlevel x (hJsq hxJ)
      fin_cases i
      · exact Or.inl hx
      · exact Or.inr hx
    have hbdy : ((D i).trans H).toHomeomorph '' sphere (0 : E2) 1 =
        (D i).toHomeomorph '' sphere (0 : E2) 1 := by
      change (H ∘ D i) '' sphere (0 : E2) 1 = D i '' sphere 0 1
      rw [image_comp]
      exact (image_congr hfix).trans (image_id _)
    have hdim : 1 < Module.rank Real E2 := by
      rw [← Module.finrank_eq_rank]
      norm_num
    have h := ((D i).trans H).toHomeomorph.image_closedBall_eq_of_image_sphere_eq
      (D i).toHomeomorph hdim hbdy
    change (H ∘ D i) '' closedBall (0 : E2) 1 = D i '' closedBall 0 1 at h
    simpa only [image_comp] using h
  have hHA := hpreserve A hAlevel
  have hHB := hpreserve B hBlevel
  have hHBinv (i : Fin 2) : H.symm '' (B i '' closedBall 0 1) = B i '' closedBall 0 1 := by
    calc
      H.symm '' (B i '' closedBall 0 1) = H.symm '' (H '' (B i '' closedBall 0 1)) :=
        congrArg (image H.symm) (hHB i).symm
      _ = B i '' closedBall 0 1 := H.toEquiv.symm_image_image _
  let Ψ (u : Real) := (H.trans (Φ u)).trans H.symm
  let L := H.symm '' K
  have hL : IsCompact L := hK.image H.symm.continuous
  have hLfix (u : Real) (x : E2) (hx : x ∉ L) : Ψ u x = x := by
    have hHx : H x ∉ K := fun hh => hx ⟨H x, hh, H.symm_apply_apply x⟩
    change H.symm (Φ u (H x)) = x
    rw [hΦfix u _ hHx, H.symm_apply_apply]
  have hLP : Disjoint L P := by
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    have he : y = H.symm y := (H.apply_symm_apply y).symm.trans (hHP _ hx)
    exact disjoint_left.mp hKP hy (he.symm ▸ hx)
  have hLsq : Disjoint L (closedSquare ρ) := by
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    have hh := (hHsq (mem_image_of_mem H hx)).2
    rw [H.apply_symm_apply] at hh
    exact hh hy
  have hmatch (i : Fin 2) : Ψ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1 := by
    change (H.symm ∘ Φ 1 ∘ H) '' (A i '' closedBall 0 1) = _
    rw [image_comp, image_comp, hHA i, hΦmatch i, hHBinv i]
  have hρr : ρ < r := hρa.trans ((haw.trans_le hwr).trans (hyperbolaRadius_lt hr ht htr))
  refine ⟨hρr, L, hL, hLP, hLsq, Ψ, ?_, ?_, ?_, hLfix, hmatch, ?_,
    H ⁻¹' W, hW.preimage H.continuous, ?_, ?_, ?_⟩
  · intro x
    change H.symm (Φ 0 (H x)) = x
    rw [hΦ0, H.symm_apply_apply]
  · exact H.symm.contDiff.comp (hΦs.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · exact H.symm.contDiff.comp (hΦi.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · intro i
    have hf (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
        frontier (D '' closedBall 0 1) = D '' sphere 0 1 := by
      have h := D.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
      rw [frontier_closedBall _ one_ne_zero] at h
      exact h.symm
    rw [← hf, ← hf, ← hmatch i]
    exact (Ψ 1).toHomeomorph.image_frontier _
  · intro x hx
    change H x ∈ W
    rw [hHP x hx]
    exact hPW hx
  · intro x hx
    exact hHsq (mem_image_of_mem H hx)
  · intro u x hx
    change H.symm (Φ u (H x)) = x
    rw [hΦV u hx.1, id_eq, H.symm_apply_apply]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
