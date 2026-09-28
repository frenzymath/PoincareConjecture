import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.FixedMorseSquare
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedFixedSquare

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private def reflectX : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![-x 0, x 1]
  invFun x := WithLp.toLp 2 ![-x 0, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.neg
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.neg
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

private theorem reflectX_twice (x : E2) : reflectX (reflectX x) = x :=
  reflectX.symm_apply_apply x

private theorem reflectX_apply (x : E2) :
    reflectX x = WithLp.toLp 2 ![-x 0, x 1] := rfl

private theorem boundary_image (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
    frontier (A '' closedBall 0 1) = A '' sphere (0 : E2) 1 := by
  have h := A.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
  rw [frontier_closedBall _ one_ne_zero] at h
  exact h.symm

theorem exists_marked_circle_pair_isotopy_fixing_morse_square
    (C D : Fin 2 → S1 → E2)
    (hC : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i))
    (hD : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hnest : ∀ i j, i ≠ j → (NestedPair (C i) (C j) ↔ NestedPair (D i) (D j)))
    {r t w a ρ : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hρ : 0 < ρ) (hρa : ρ < a) (haw : a < w) (hwr : w ≤ hyperbolaRadius r t)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈ range (C i) ∩ range (D i))
    (hClevel : ∀ x ∈ openSquare r, x ∈ range (C 0) ∪ range (C 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hDlevel : ∀ x ∈ openSquare r, x ∈ range (D 0) ∪ range (D 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    ρ < r ∧ ∃ K : Set E2, IsCompact K ∧ Disjoint K (closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' range (C i) = range (D i)) ∧
        ∃ U : Set E2, IsOpen U ∧ closedSquare ρ ⊆ U ∧ ∀ u, EqOn (Φ u) id U := by
  classical
  choose A hA using fun i => exists_ambient_diffeomorph_of_smooth_circle (C i) (hC i)
  choose B hB using fun i => exists_ambient_diffeomorph_of_smooth_circle (D i) (hD i)
  have hn (i j : Fin 2) (hij : i ≠ j) :
      (A i '' closedBall 0 1 ⊆ A j '' ball 0 1) ↔
        B i '' closedBall 0 1 ⊆ B j '' ball 0 1 := by
    rw [← nestedPair_iff_of_normalizations (C i) (C j) (A i) (A j) (hA i) (hA j),
      ← nestedPair_iff_of_normalizations (D i) (D j) (B i) (B j) (hB i) (hB j)]
    exact hnest i j hij
  have he : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1) := by
    intro i s hs
    rw [hA i, hB i]
    exact hedge i s hs
  have hAl : ∀ x ∈ openSquare r,
      x ∈ (A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t := by simpa only [hA] using hClevel
  have hBl : ∀ x ∈ openSquare r,
      x ∈ (B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t := by simpa only [hB] using hDlevel
  have hresult : ∃ K : Set E2, IsCompact K ∧ Disjoint K (closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        ∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1 := by
    by_cases h10 : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1
    · obtain ⟨_, K, hK, _, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch, _⟩ :=
        exists_nested_disk_pair_isotopy_fixing_entire_negative_morse_square A B h10
          ((hn 1 0 (by decide)).mp h10) hr ht htr hρ hρa haw hwr he hAl hBl
      exact ⟨K, hK, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch⟩
    by_cases h01 : A 0 '' closedBall 0 1 ⊆ A 1 '' ball 0 1
    · let swap : Fin 2 → Fin 2 := fun i => 1 - i
      have hswap (i : Fin 2) : swap (swap i) = i := by fin_cases i <;> rfl
      let A' (i : Fin 2) := (A (swap i)).trans reflectX
      let B' (i : Fin 2) := (B (swap i)).trans reflectX
      have hA' : A' 1 '' closedBall 0 1 ⊆ A' 0 '' ball 0 1 := by
        change (reflectX ∘ A 0) '' closedBall 0 1 ⊆ (reflectX ∘ A 1) '' ball 0 1
        simpa only [image_comp] using image_mono (f := reflectX) h01
      have hB' : B' 1 '' closedBall 0 1 ⊆ B' 0 '' ball 0 1 := by
        change (reflectX ∘ B 0) '' closedBall 0 1 ⊆ (reflectX ∘ B 1) '' ball 0 1
        simpa only [image_comp] using image_mono (f := reflectX) ((hn 0 1 (by decide)).mp h01)
      have hedgeflip (i : Fin 2) (s : Real) :
          reflectX (negativeLevelRibbon t (WithLp.toLp 2 ![s, (swap i : Real)])) =
            negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) := by
        fin_cases i <;> ext j <;> fin_cases j <;>
          norm_num [reflectX_apply, swap, negativeLevelRibbon, positiveLevelRibbon, saddleCoordinateSwap]
      have he' : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
          negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
            (A' i '' sphere (0 : E2) 1) ∩ (B' i '' sphere (0 : E2) 1) := by
        intro i s hs
        obtain ⟨ha, hb⟩ := he (swap i) s hs
        constructor
        · change _ ∈ (reflectX ∘ A (swap i)) '' sphere (0 : E2) 1
          rw [image_comp, ← hedgeflip i s]
          exact mem_image_of_mem _ ha
        · change _ ∈ (reflectX ∘ B (swap i)) '' sphere (0 : E2) 1
          rw [image_comp, ← hedgeflip i s]
          exact mem_image_of_mem _ hb
      have hflip_level (F : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
          (hl : ∀ x ∈ openSquare r,
            x ∈ (F 0 '' sphere (0 : E2) 1) ∪ (F 1 '' sphere (0 : E2) 1) →
              -(x 0)^2 + (x 1)^2 = -t) :
          ∀ x ∈ openSquare r,
            x ∈ ((F (swap 0)).trans reflectX '' sphere (0 : E2) 1) ∪
              ((F (swap 1)).trans reflectX '' sphere (0 : E2) 1) →
              -(x 0)^2 + (x 1)^2 = -t := by
        intro x hx hm
        have hxR : reflectX x ∈ openSquare r := by simpa [reflectX_apply, openSquare] using hx
        have hmR : reflectX x ∈ (F 0 '' sphere (0 : E2) 1) ∪ (F 1 '' sphere (0 : E2) 1) := by
          rcases hm with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
          · right
            refine ⟨y, hy, ?_⟩
            have hh := congrArg reflectX hxy
            change reflectX (reflectX (F 1 y)) = reflectX x at hh
            simpa only [reflectX_twice] using hh
          · left
            refine ⟨y, hy, ?_⟩
            have hh := congrArg reflectX hxy
            change reflectX (reflectX (F 0 y)) = reflectX x at hh
            simpa only [reflectX_twice] using hh
        simpa [reflectX_apply] using hl (reflectX x) hxR hmR
      obtain ⟨_, K, hK, _, hKsq, Ψ, h0, hΨ, hΨi, hfix, hmatch, _⟩ :=
        exists_nested_disk_pair_isotopy_fixing_entire_negative_morse_square A' B' hA' hB'
          hr ht htr hρ hρa haw hwr he' (hflip_level A hAl) (hflip_level B hBl)
      let Φ (u : Real) := (reflectX.trans (Ψ u)).trans reflectX
      refine ⟨reflectX '' K, hK.image reflectX.continuous, ?_, Φ, ?_, ?_, ?_, ?_, ?_⟩
      · apply disjoint_left.mpr
        rintro x ⟨y, hy, rfl⟩ hx
        exact disjoint_left.mp hKsq hy (by simpa [reflectX_apply, closedSquare] using hx)
      · intro x
        change reflectX (Ψ 0 (reflectX x)) = x
        rw [h0, reflectX_twice]
      · exact reflectX.contDiff.comp
          (hΨ.comp (contDiff_fst.prodMk (reflectX.contDiff.comp contDiff_snd)))
      · exact reflectX.contDiff.comp
          (hΨi.comp (contDiff_fst.prodMk (reflectX.contDiff.comp contDiff_snd)))
      · intro u x hx
        have hnK : reflectX x ∉ K := fun hh => hx ⟨reflectX x, hh, reflectX_twice x⟩
        change reflectX (Ψ u (reflectX x)) = x
        rw [hfix u _ hnK, reflectX_twice]
      · intro i
        have hm := hmatch (swap i)
        change Ψ 1 '' ((reflectX ∘ A (swap (swap i))) '' closedBall 0 1) =
          (reflectX ∘ B (swap (swap i))) '' closedBall 0 1 at hm
        rw [hswap, image_comp, image_comp] at hm
        change (reflectX ∘ Ψ 1 ∘ reflectX) '' (A i '' closedBall 0 1) = _
        rw [image_comp, image_comp, hm, ← image_comp]
        simp only [Function.comp_def, reflectX_twice]
        exact image_id _
    have hdim : 1 < Module.rank Real E2 := by rw [← Module.finrank_eq_rank]; norm_num
    have hAdis : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1) := by
      have hs : Disjoint (A 0 '' sphere (0 : E2) 1) (A 1 '' sphere (0 : E2) 1) := by
        rwa [hA 0, hA 1]
      rcases (A 0).toHomeomorph.disjoint_or_nested_image_closedBall
        (A 1).toHomeomorph hdim hs with h | h | h
      · exact h
      · exact (h01 h).elim
      · exact (h10 h).elim
    have hBdis : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1) := by
      have hs : Disjoint (B 0 '' sphere (0 : E2) 1) (B 1 '' sphere (0 : E2) 1) := by
        rwa [hB 0, hB 1]
      rcases (B 0).toHomeomorph.disjoint_or_nested_image_closedBall
        (B 1).toHomeomorph hdim hs with h | h | h
      · exact h
      · exact (h01 ((hn 0 1 (by decide)).mpr h)).elim
      · exact (h10 ((hn 1 0 (by decide)).mpr h)).elim
    obtain ⟨_, K, hK, _, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch, _⟩ :=
      exists_disk_pair_isotopy_fixing_entire_negative_morse_square A B hAdis hBdis
        hr ht htr (hρ.trans (hρa.trans haw)) hwr hρ hρa haw
        (by simpa using he 0) (by simpa using he 1)
        (by simpa only [boundary_image] using hAl) (by simpa only [boundary_image] using hBl)
    exact ⟨K, hK, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch⟩
  obtain ⟨K, hK, hKsq, Φ, h0, hΦ, hΦi, hfix, hmatch⟩ := hresult
  refine ⟨hρa.trans ((haw.trans_le hwr).trans (hyperbolaRadius_lt hr ht htr)),
    K, hK, hKsq, Φ, h0, hΦ, hΦi, hfix, ?_, Kᶜ, hK.isClosed.isOpen_compl, ?_, ?_⟩
  · intro i
    rw [← hA i, ← hB i, ← boundary_image, ← boundary_image, ← hmatch i]
    exact (Φ 1).toHomeomorph.image_frontier _
  · intro x hx hmem
    exact disjoint_left.mp hKsq hmem hx
  · intro u x hx
    exact hfix u x hx

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
