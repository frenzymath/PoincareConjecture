import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PrescribedMorse
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

private theorem disk_preserved_of_fixed_boundary
    (D H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hfix : ∀ x ∈ D '' sphere (0 : E2) 1, H x = x) :
    H '' (D '' closedBall 0 1) = D '' closedBall 0 1 := by
  have hbdy : (D.trans H).toHomeomorph '' sphere (0 : E2) 1 =
      D.toHomeomorph '' sphere (0 : E2) 1 := by
    change (H ∘ D) '' sphere (0 : E2) 1 = D '' sphere 0 1
    rw [image_comp]
    exact (image_congr hfix).trans (image_id _)
  have hdim : 1 < Module.rank Real E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have h := (D.trans H).toHomeomorph.image_closedBall_eq_of_image_sphere_eq
    D.toHomeomorph hdim hbdy
  change (H ∘ D) '' closedBall (0 : E2) 1 = D '' closedBall 0 1 at h
  simpa only [image_comp] using h




theorem exists_disk_pair_isotopy_fixing_entire_negative_morse_square
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (hB : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1))
    {r t w a ρ : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hw : 0 < w) (hwr : w ≤ hyperbolaRadius r t)
    (hρ : 0 < ρ) (hρa : ρ < a) (haw : a < w)
    (hstart : ∀ s ∈ Ioo (-w) w, negativeLevelArc t 1 s ∈
      (A 0 '' sphere (0 : E2) 1) ∩ (B 0 '' sphere (0 : E2) 1))
    (hfinish : ∀ s ∈ Ioo (-w) w, negativeLevelArc t 0 s ∈
      (A 1 '' sphere (0 : E2) 1) ∩ (B 1 '' sphere (0 : E2) 1))
    (hAlevel : ∀ x ∈ openSquare r,
      x ∈ frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hBlevel : ∀ x ∈ openSquare r,
      x ∈ frontier (B 0 '' closedBall 0 1) ∪ frontier (B 1 '' closedBall 0 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    ρ < r ∧ ∃ K : Set E2, IsCompact K ∧
      Disjoint K ((fun z : Real × Real =>
        negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
          (Icc (-a) a ×ˢ Icc 0 1)) ∧
      Disjoint K (closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧
          ((fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
            (Icc (-a) a ×ˢ Icc 0 1)) ⊆ U ∧
          closedSquare ρ ⊆ U ∧ ∀ u, EqOn (Φ u) id U := by
  have ha : 0 < a := hρ.trans hρa
  let σ := min a (Real.sqrt t)
  have hσ : 0 < σ := lt_min ha (Real.sqrt_pos.mpr ht)
  obtain ⟨_, K, hK, hKP, _, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦmatch,
      V, hV, hPV, _, hΦV⟩ :=
    exists_disk_pair_isotopy_fixing_prescribed_negative_morse_square
      A B hA hB hr ht htr hw hwr ha haw hσ (min_le_left _ _) (min_le_right _ _)
      hstart hfinish hAlevel hBlevel
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
        x ∈ frontier (D 0 '' closedBall 0 1) ∪ frontier (D 1 '' closedBall 0 1) →
        -(x 0)^2 + (x 1)^2 = -t) (i : Fin 2) :
      H '' (D i '' closedBall 0 1) = D i '' closedBall 0 1 := by
    apply disk_preserved_of_fixed_boundary
    intro x hx
    apply hHfix
    intro hxJ
    apply disjoint_left.mp hJlevel hxJ
    apply hlevel x (hJsq hxJ)
    have hfront : x ∈ frontier (D i '' closedBall 0 1) := by
      have he := (D i).toHomeomorph.image_frontier (closedBall (0 : E2) 1)
      rw [frontier_closedBall (0 : E2) one_ne_zero] at he
      exact he ▸ hx
    fin_cases i
    · exact Or.inl hfront
    · exact Or.inr hfront
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
  have hρr : ρ < r := hρa.trans ((haw.trans_le hwr).trans (hyperbolaRadius_lt hr ht htr))
  refine ⟨hρr, L, hL, hLP, hLsq, Ψ, ?_, ?_, ?_, hLfix, ?_,
    H ⁻¹' W, hW.preimage H.continuous, ?_, ?_, ?_⟩
  · intro x
    change H.symm (Φ 0 (H x)) = x
    rw [hΦ0, H.symm_apply_apply]
  · exact H.symm.contDiff.comp (hΦs.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · exact H.symm.contDiff.comp (hΦi.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · intro i
    change (H.symm ∘ Φ 1 ∘ H) '' (A i '' closedBall 0 1) = _
    rw [image_comp, image_comp, hHA i, hΦmatch i, hHBinv i]
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
