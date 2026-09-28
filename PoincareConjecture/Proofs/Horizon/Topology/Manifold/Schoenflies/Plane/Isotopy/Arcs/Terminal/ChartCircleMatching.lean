import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.MarkedCircleMatching
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem smoothEmbedding_postcomp
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {C : S1 → E2}
    (hC : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ C) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (Q ∘ C) := by
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (Q.contMDiff.comp hC.contMDiff) (Q.injective.comp hC.isEmbedding.injective)
  intro q
  rw [mfderiv_comp q (Q.contMDiff.mdifferentiable (by simp) _)
    (hC.contMDiff.mdifferentiable (by simp) q)]
  exact (Q.mfderivToContinuousLinearEquiv (by simp) (C q)).injective.comp
    ((hC.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))

private theorem nestedPair_postcomp
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {C D : S1 → E2}
    (h : NestedPair C D) : NestedPair (Q ∘ C) (Q ∘ D) := by
  obtain ⟨F, hF, hin⟩ := h
  refine ⟨F.trans Q, ?_, ?_⟩
  · change (Q ∘ F) '' sphere (0 : E2) 1 = range (Q ∘ D)
    rw [image_comp, hF, range_comp]
  · rintro x ⟨q, rfl⟩
    obtain ⟨u, hu, he⟩ := hin (mem_range_self q)
    exact ⟨u, hu, congrArg Q he⟩

private theorem nestedPair_postcomp_iff
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (C D : S1 → E2) :
    NestedPair (Q ∘ C) (Q ∘ D) ↔ NestedPair C D := by
  constructor
  · intro h
    simpa only [comp_def, Q.symm_apply_apply] using nestedPair_postcomp Q.symm h
  · exact nestedPair_postcomp Q

private theorem mem_pulledback_circle
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (C : S1 → E2) (x : E2) :
    x ∈ range (R.symm ∘ C) ↔ R x ∈ range C := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, (R.apply_symm_apply _).symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by change R.symm (C q) = x; rw [hq, R.symm_apply_apply]⟩

theorem exists_chart_marked_circle_pair_isotopy_fixing_morse_square
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (C D : Fin 2 → S1 → E2)
    (hC : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i))
    (hD : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hnest : ∀ i j, i ≠ j → (NestedPair (C i) (C j) ↔ NestedPair (D i) (D j)))
    {r t w a ρ : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hρ : 0 < ρ) (hρa : ρ < a) (haw : a < w) (hwr : w ≤ hyperbolaRadius r t)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      R (negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)])) ∈
        range (C i) ∩ range (D i))
    (hClevel : ∀ x ∈ openSquare r, R x ∈ range (C 0) ∪ range (C 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hDlevel : ∀ x ∈ openSquare r, R x ∈ range (D 0) ∪ range (D 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    ρ < r ∧ ∃ K : Set E2, IsCompact K ∧ Disjoint K (R '' closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' range (C i) = range (D i)) ∧
        ∃ U : Set E2, IsOpen U ∧ R '' closedSquare ρ ⊆ U ∧
          ∀ u, EqOn (Φ u) id U := by
  let C' : Fin 2 → S1 → E2 := fun i => R.symm ∘ C i
  let D' : Fin 2 → S1 → E2 := fun i => R.symm ∘ D i
  have hC' (i : Fin 2) : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C' i) :=
    smoothEmbedding_postcomp R.symm (hC i)
  have hD' (i : Fin 2) : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D' i) :=
    smoothEmbedding_postcomp R.symm (hD i)
  have hC'dis : Disjoint (range (C' 0)) (range (C' 1)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hCdis ((mem_pulledback_circle R (C 0) x).mp hx)
      ((mem_pulledback_circle R (C 1) x).mp hy)
  have hD'dis : Disjoint (range (D' 0)) (range (D' 1)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hDdis ((mem_pulledback_circle R (D 0) x).mp hx)
      ((mem_pulledback_circle R (D 1) x).mp hy)
  have hn (i j : Fin 2) (hij : i ≠ j) :
      NestedPair (C' i) (C' j) ↔ NestedPair (D' i) (D' j) :=
    (nestedPair_postcomp_iff R.symm (C i) (C j)).trans
      ((hnest i j hij).trans (nestedPair_postcomp_iff R.symm (D i) (D j)).symm)
  have he (i : Fin 2) (s : Real) (hs : s ∈ Ioo (-w) w) :
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
        range (C' i) ∩ range (D' i) :=
    ⟨(mem_pulledback_circle R (C i) _).mpr (hedge i s hs).1,
      (mem_pulledback_circle R (D i) _).mpr (hedge i s hs).2⟩
  have hCl (x : E2) (hx : x ∈ openSquare r)
      (hm : x ∈ range (C' 0) ∪ range (C' 1)) : -(x 0)^2 + (x 1)^2 = -t := by
    apply hClevel x hx
    exact hm.imp ((mem_pulledback_circle R (C 0) x).mp)
      ((mem_pulledback_circle R (C 1) x).mp)
  have hDl (x : E2) (hx : x ∈ openSquare r)
      (hm : x ∈ range (D' 0) ∪ range (D' 1)) : -(x 0)^2 + (x 1)^2 = -t := by
    apply hDlevel x hx
    exact hm.imp ((mem_pulledback_circle R (D 0) x).mp)
      ((mem_pulledback_circle R (D 1) x).mp)
  obtain ⟨hρr, K, hK, hKsq, Ψ, h0, hΨ, hΨi, hfix, hmatch, U, hU, hsqU, hUfix⟩ :=
    exists_marked_circle_pair_isotopy_fixing_morse_square C' D' hC' hD' hC'dis hD'dis
      hn hr ht htr hρ hρa haw hwr he hCl hDl
  let Φ (u : Real) := (R.symm.trans (Ψ u)).trans R
  refine ⟨hρr, R '' K, hK.image R.continuous, ?_, Φ, ?_, ?_, ?_, ?_, ?_,
    R '' U, R.toHomeomorph.isOpenMap _ hU, image_mono hsqU, ?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    exact disjoint_left.mp hKsq hy ((R.injective heq) ▸ hz)
  · intro x
    change R (Ψ 0 (R.symm x)) = x
    rw [h0, R.apply_symm_apply]
  · exact R.contDiff.comp
      (hΨ.comp (contDiff_fst.prodMk (R.symm.contDiff.comp contDiff_snd)))
  · exact R.contDiff.comp
      (hΨi.comp (contDiff_fst.prodMk (R.symm.contDiff.comp contDiff_snd)))
  · intro u x hx
    have hnK : R.symm x ∉ K := fun hh => hx ⟨R.symm x, hh, R.apply_symm_apply x⟩
    change R (Ψ u (R.symm x)) = x
    rw [hfix u _ hnK, R.apply_symm_apply]
  · intro i
    change (R ∘ Ψ 1 ∘ R.symm) '' range (C i) = range (D i)
    rw [image_comp, image_comp, ← range_comp, hmatch i]
    change R '' range (R.symm ∘ D i) = range (D i)
    rw [← range_comp]
    simp only [comp_def, R.apply_symm_apply]
  · intro u x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change R (Ψ u (R.symm (R y))) = R y
    rw [R.symm_apply_apply, hUfix u hy]
    rfl

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
