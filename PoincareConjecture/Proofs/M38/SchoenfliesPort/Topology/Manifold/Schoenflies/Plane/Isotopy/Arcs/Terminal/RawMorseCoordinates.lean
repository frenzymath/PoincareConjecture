import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PlanarChart







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

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_terminal_raw_morse_coordinates
    (hg : g ∈ M.tree.leaves)
    (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hJ : ∀ y, J y 2 = inner Real (M.v : E3) y)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ closedSquare r ⊆ e.source ∧
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∈ closedSquare r, R x = Saddle.toE2 (J (g (e x)))) ∧
        ∀ x ∈ closedSquare r, ∀ t ∈ Icc (-δ) δ,
          Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ J '' range g ↔
            -x 0 ^ 2 + x 1 ^ 2 = t := by
  obtain ⟨a, ha, has, R, hR⟩ :=
    exists_terminal_planar_chart_before_flattening hg J hJ he0 hep he hei hc
  let F : S2 → E3 := J ∘ g
  let c := inner Real (M.v : E3) (g p)
  have hheight (q : S2) : F q 2 = inner Real (M.v : E3) (g q) := hJ _
  have hFi : Topology.IsEmbedding F :=
    J.toHomeomorph.isEmbedding.comp (M.tree.embedding_of_mem_leaves hg).isEmbedding
  have hU : IsOpen (e '' ball (0 : E2) a) :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans has)
  obtain ⟨V, hV, hFV⟩ := hFi.isInducing.isOpen_iff.mp hU
  have hpV : F p ∈ V := by
    change p ∈ F ⁻¹' V
    rw [hFV]
    exact ⟨0, mem_ball_self ha, hep⟩
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
  have hL0 : L (0, 0) = F p := by
    have hr0 := hR 0 (mem_closedBall_self ha.le)
    rw [hep] at hr0
    ext i
    fin_cases i
    · exact congrArg (fun x : E2 => x 0) hr0
    · exact congrArg (fun x : E2 => x 1) hr0
    · simpa [L, Saddle.toE3, c] using (hheight p).symm
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp
    ((hV.preimage hL).mem_nhds (show (0, 0) ∈ L ⁻¹' V by
      change L (0, 0) ∈ V
      rw [hL0]
      exact hpV))
  let r := min a ε / 4
  let δ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hδ : 0 < δ := half_pos hε
  have hra : 2 * r < a := by
    have := min_le_left a ε
    dsimp [r] at hr ⊢
    linarith
  have hrε : 2 * r < ε := by
    have := min_le_right a ε
    dsimp [r] at hr ⊢
    linarith
  have hδε : δ < ε := half_lt_self hε
  have hrball : closedSquare r ⊆ closedBall (0 : E2) a := by
    intro x hx
    exact le_trans (closedSquare_subset_closedBall hr.le hx) hra.le
  have hrsource : closedSquare r ⊆ e.source := hrball.trans has
  have hinside (x : E2) (hx : x ∈ closedSquare r) (t : Real) (ht : t ∈ Icc (-δ) δ) :
      L (x, t) ∈ V := by
    apply hεV
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq, sub_zero]
    exact ⟨(mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall hr.le hx)).trans_lt hrε,
      (abs_le.mpr ht).trans_lt hδε⟩
  refine ⟨r, δ, hr, hδ, hrsource, R, fun x hx => hR x (hrball hx), ?_⟩
  intro x hx t ht
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, hq⟩
    have hqV : F q ∈ V := by
      rw [show F q = L (x, t) from hq]
      exact hinside x hx t ht
    have hqpatch : q ∈ e '' ball (0 : E2) a := by
      rw [← hFV]
      exact hqV
    obtain ⟨y, hy, rfl⟩ := hqpatch
    have hRy : R y = R x := by
      rw [hR y (ball_subset_closedBall hy)]
      ext i
      fin_cases i
      · exact congrArg (fun z : E3 => z 0) hq
      · exact congrArg (fun z : E3 => z 1) hq
    have hyx := R.injective hRy
    subst y
    have hht := congrArg (fun z : E3 => z 2) hq
    change F (e x) 2 = c + t at hht
    rw [hheight, hform x (hrsource hx)] at hht
    dsimp [c] at hht
    linarith
  · intro hxt
    refine ⟨g (e x), mem_range_self _, ?_⟩
    have hxR := hR x (hrball hx)
    have hxheight := hheight (e x)
    rw [hform x (hrsource hx)] at hxheight
    ext i
    fin_cases i
    · exact (congrArg (fun z : E2 => z 0) hxR).symm
    · exact (congrArg (fun z : E2 => z 1) hxR).symm
    · change F (e x) 2 = c + t
      dsimp [c]
      linarith

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
