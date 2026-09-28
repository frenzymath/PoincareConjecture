import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RawMorseCoordinates
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.NestedSlab







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_terminal_raw_matched_morse_coordinates
    {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (hg : g ∈ M.tree.leaves)
    (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hJ : ∀ y, J y 2 = inner Real (M.v : E3) y)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {d : OpenPartialHomeomorph E2 S2} {s u : Real} (hs : 0 < s) (hu : 0 < u)
    (hd : closedBall (0 : E2) u ⊆ d.source)
    (hea : ∀ x ∈ closedBall (0 : E2) u, Real.sqrt s • x ∈ e.source)
    (hmatch : ∀ x ∈ closedBall (0 : E2) u,
      F (d x) = g (e (Real.sqrt s • x))) :
    ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ closedSquare r ⊆ e.source ∧
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∈ closedSquare r, R x = Saddle.toE2 (J (g (e x)))) ∧
        ∀ x ∈ closedSquare r, ∀ t ∈ Icc (-δ) δ,
          (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ J '' range g ↔
            -x 0 ^ 2 + x 1 ^ 2 = t) ∧
          (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
            J '' (F '' sphere (0 : E3) 1) ↔ -x 0 ^ 2 + x 1 ^ 2 = t) := by
  obtain ⟨a, b, ha, hb, has, R, hR, hlevel⟩ :=
    exists_terminal_raw_morse_coordinates hg J hJ he0 hep he hei hc hform
  have hge := M.tree.embedding_of_mem_leaves hg
  obtain ⟨U, hU, hpoint, hcommon⟩ := Saddle.Nested.exists_common_neighborhood_of_matching
    hge.contMDiff.continuous hge.isEmbedding.injective F J hs (le_refl (0 : Real))
    (by simpa using mul_pos (Real.sqrt_pos.mpr hs) hu) hd hea hmatch
  have hpU : J (g p) ∈ U := by
    apply hpoint
    exact ⟨0, by simp [closedSquare], by simp only [hep]⟩
  let c := inner Real (M.v : E3) (g p)
  let L : E2 × Real → E3 := fun z => Saddle.toE3 (R z.1) (c + z.2)
  have hL : Continuous L := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp
        (R.contMDiff.contDiff.comp contDiff_fst)
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp
        (R.contMDiff.contDiff.comp contDiff_fst)
    · exact contDiff_const.add contDiff_snd
  have hL0 : L (0, 0) = J (g p) := by
    have hR0 := hR 0 (by simp [closedSquare, ha.le])
    rw [hep] at hR0
    ext i
    fin_cases i
    · exact congrArg (fun x : E2 => x 0) hR0
    · exact congrArg (fun x : E2 => x 1) hR0
    · simpa [L, Saddle.toE3, c] using (hJ (g p)).symm
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage hL).mem_nhds (show (0, 0) ∈ L ⁻¹' U by
      change L (0, 0) ∈ U
      rwa [hL0]))
  let r := min a ε / 4
  let δ := min b ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hra : r ≤ a := by dsimp [r]; linarith [min_le_left a ε]
  have hrε : 2 * r < ε := by dsimp [r] at hr ⊢; linarith [min_le_right a ε]
  have hδb : δ ≤ b := by dsimp [δ]; linarith [min_le_left b ε]
  have hδε : δ < ε := by dsimp [δ] at hδ ⊢; linarith [min_le_right b ε]
  have hsub : closedSquare r ⊆ closedSquare a := fun x hx =>
    ⟨hx.1.trans hra, hx.2.trans hra⟩
  refine ⟨r, δ, hr, hδ, hsub.trans has, R, fun x hx => hR x (hsub hx), ?_⟩
  intro x hx t ht
  have ht' : t ∈ Icc (-b) b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hactual := hlevel x (hsub hx) t ht'
  have hinside : L (x, t) ∈ U := by
    apply hεU
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq, sub_zero]
    exact ⟨(mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall hr.le hx)).trans_lt hrε,
      (abs_le.mpr ht).trans_lt hδε⟩
  refine ⟨hactual, ?_⟩
  have heq : L (x, t) ∈ J '' range g ↔
      L (x, t) ∈ (F.trans J) '' sphere (0 : E3) 1 := by
    have hm := Set.ext_iff.mp hcommon (L (x, t))
    simpa only [mem_inter_iff, hinside, and_true] using hm
  have himage : (F.trans J) '' sphere (0 : E3) 1 =
      J '' (F '' sphere (0 : E3) 1) := by
    rw [image_image]
    rfl
  rw [himage] at heq
  exact heq.symm.trans hactual

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
