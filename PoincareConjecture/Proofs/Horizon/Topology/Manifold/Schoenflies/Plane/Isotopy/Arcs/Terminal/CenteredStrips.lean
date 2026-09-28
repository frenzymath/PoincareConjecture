import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CenteredCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualStripData



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_strip_closed_rectangle (d : TerminalSaddleGeometry M P p e)
    (s : ActualStripData d) (i : Fin 2) :
    Icc (d.a i) (d.b i) ×ˢ Icc (-d.delta) d.delta ⊆ (d.strips i).source := by
  intro z hz
  rw [s.source_eq]
  have hdw := s.delta_lt_bandHeight.trans s.bandHeight_lt_width
  exact ⟨⟨by linarith [hz.1.1, s.width_pos], by linarith [hz.1.2, s.width_pos]⟩,
    ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩

theorem terminal_centered_strip_height (d : TerminalSaddleGeometry M P p e)
    (s : ActualStripData d) (i : Fin 2) (z : Real × Real) (hz : z ∈ (d.strips i).source) :
    terminalCenteredFrame d (g (d.strips i z)) 2 = z.2 := by
  rw [terminalCenteredFrame_height, s.height i z hz]
  ring

theorem terminal_centered_strip_flattening (d : TerminalSaddleGeometry M P p e)
    (s : ActualStripData d) (i : Fin 2) (x : Real) (hx : x ∈ Icc (d.a i) (d.b i))
    (t : Real) (ht : t ∈ Icc (-d.delta) d.delta) :
    terminalCenteredFlattening d (terminalCenteredFrame d (g (d.strips i (x, t)))) =
      terminalCenteredFrame d (g (d.strips i (x, 0))) +
        t • (EuclideanSpace.single 2 1 : E3) := by
  rw [terminalCenteredFlattening_apply_frame, s.flattening i t
    ⟨by linarith [ht.1, s.delta_lt_bandHeight], ht.2.trans s.delta_lt_bandHeight.le⟩ x hx,
    terminalCenteredFrame_translate]


def terminalActualTrace (d : TerminalSaddleGeometry M P p e) : Set E2 :=
  ⋃ i, (fun x => Saddle.toE2 (terminalCenteredFrame d (g (d.strips i (x, 0))))) ''
    Icc (d.a i) (d.b i)

private theorem lift_projection {y : E3} {t : Real} (hy : y 2 = t) :
    Saddle.toE3 (Saddle.toE2 y) t = y := by
  ext i
  fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hy]

private theorem projection_translate (y : E3) (t : Real) :
    Saddle.toE2 (y + t • (EuclideanSpace.single 2 1 : E3)) = Saddle.toE2 y := by
  ext i
  fin_cases i <;> simp [Saddle.toE2, PiLp.add_apply, PiLp.smul_apply]



theorem terminal_centered_actual_level_eq_open_patch_union_trace
    (d : TerminalSaddleGeometry M P p e) (s : ActualStripData d)
    (t : Real) (ht : t ∈ Icc (-d.delta) d.delta) :
    range (fun q => terminalCenteredFlattening d (terminalCenteredFrame d (g q))) ∩
        {y : E3 | y 2 = t} =
      ((fun q => terminalCenteredFlattening d (terminalCenteredFrame d (g q))) ''
        (e '' openSquare d.r) ∩ {y : E3 | y 2 = t}) ∪
      Saddle.slice (terminalActualTrace d) t := by
  let F : S2 → E3 := fun q => terminalCenteredFlattening d (terminalCenteredFrame d (g q))
  have hFheight (q) : F q 2 = inner Real (M.v : E3) (g q) - inner Real (M.v : E3) (g p) := by
    dsimp only [F]
    rw [terminalCenteredFlattening_height, terminalCenteredFrame_height]
  have htrace (i : Fin 2) (x : Real) (hx : x ∈ Icc (d.a i) (d.b i)) :
      F (d.strips i (x, t)) = Saddle.toE3
        (Saddle.toE2 (terminalCenteredFrame d (g (d.strips i (x, 0))))) t := by
    have hz := terminal_centered_strip_height d s i (x, t)
      (terminal_strip_closed_rectangle d s i ⟨hx, ht⟩)
    have hFz : F (d.strips i (x, t)) 2 = t := by
      dsimp only [F]
      rw [terminalCenteredFlattening_height]
      exact hz
    have hproj : Saddle.toE2 (F (d.strips i (x, t))) =
        Saddle.toE2 (terminalCenteredFrame d (g (d.strips i (x, 0)))) := by
      dsimp only [F]
      rw [terminal_centered_strip_flattening d s i x hx t ht, projection_translate]
    rw [← hproj]
    exact (lift_projection hFz).symm
  ext y
  constructor
  · rintro ⟨⟨q, rfl⟩, hqt⟩
    have hqheight : inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p) + t := by
      change F q 2 = t at hqt
      rw [hFheight] at hqt
      linarith
    have hqband : q ∈ (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
        Icc (inner Real (M.v : E3) (g p) - s.bandHeight)
          (inner Real (M.v : E3) (g p) + s.bandHeight) := by
      change inner Real (M.v : E3) (g p) - s.bandHeight ≤ inner Real (M.v : E3) (g q) ∧
        inner Real (M.v : E3) (g q) ≤ inner Real (M.v : E3) (g p) + s.bandHeight
      rw [hqheight]
      constructor <;> linarith [ht.1, ht.2, s.delta_lt_bandHeight]
    rcases s.band_cover hqband with hpatch | hstrip
    · exact Or.inl ⟨mem_image_of_mem F hpatch, hqt⟩
    · obtain ⟨i, ⟨x, u⟩, ⟨hx, hu⟩, heq⟩ := mem_iUnion.mp hstrip
      have hut : u = t := by
        have hsrc : (x, u) ∈ (d.strips i).source := by
          rw [s.source_eq]
          exact ⟨⟨by linarith [hx.1, s.width_pos], by linarith [hx.2, s.width_pos]⟩,
            ⟨by linarith [hu.1, s.bandHeight_lt_width],
              by linarith [hu.2, s.bandHeight_lt_width]⟩⟩
        have hh := s.height i (x, u) hsrc
        rw [heq, hqheight] at hh
        linarith
      subst u
      apply Or.inr
      change F q ∈ Saddle.slice (terminalActualTrace d) t
      rw [← heq, htrace i x hx]
      refine ⟨?_, rfl⟩
      change Saddle.toE2 (terminalCenteredFrame d (g (d.strips i (x, 0)))) ∈ terminalActualTrace d
      exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  · intro hy
    rcases hy with ⟨⟨q, _, rfl⟩, hz⟩ | hz
    · exact ⟨mem_range_self q, hz⟩
    · obtain ⟨i, u, hu, heq⟩ := mem_iUnion.mp hz.1
      change Saddle.toE2 (terminalCenteredFrame d (g (d.strips i (u, 0)))) = Saddle.toE2 y at heq
      refine ⟨⟨d.strips i (u, t), (htrace i u hu).trans ?_⟩, hz.2⟩
      rw [heq]
      exact lift_projection hz.2

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
