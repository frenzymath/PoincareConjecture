import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Family.ActualAnnuli
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_slab_avoiding_inserted_caps
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) :
    ∃ a b : Real, a < data.ends.lowerCut ∧ data.ends.upperCut < b ∧
      ∀ D ∈ data.ends.caps, ∀ q ∈ D.chart '' closedBall (0 : E2) 1,
        inner Real (M.v : E3) (g q) ≤ a ∨ b ≤ inner Real (M.v : E3) (g q) := by
  have hg' := M.tree.embedding_of_mem_leaves hg
  obtain ⟨a, δa, hδa, _, hgapA, hcentersA, _⟩ :=
    data.ends.exists_lower_common_physical_annuli hg' (norm_eq_of_mem_sphere M.v)
  obtain ⟨b, δb, hδb, _, hgapB, hcentersB, _⟩ :=
    data.ends.exists_upper_common_physical_annuli hg' (norm_eq_of_mem_sphere M.v)
  refine ⟨a, b, by linarith, by linarith, ?_⟩
  intro D hD q hq
  rcases data.ends.cap_side D hD with hlow | hupp
  · left
    have hc := hcentersA ⟨⟨D, hD⟩, hlow⟩
    have hh := (data.ends.lower D hD hlow).height_le_center_of_mem_cap hq
    dsimp only at hc
    linarith
  · right
    have hc := hcentersB ⟨⟨D, hD⟩, hupp⟩
    have hh := (data.ends.upper D hD hupp).reflected.height_le_center_of_mem_cap hq
    change inner Real (M.v : E3) (heightReflection D.unit_v (g q)) ≤ -D.center at hh
    rw [inner_heightReflection] at hh
    dsimp only at hc
    linarith

theorem exists_terminal_core_free_slabs
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) :
    ∃ R : Real, 0 < R ∧
      ∀ c : Real, c = data.ends.lowerCut ∨ c = data.ends.upperCut →
      ∀ D ∈ data.ends.caps, ∀ q ∈ D.chart '' closedBall (0 : E2) 1,
        R < |inner Real (M.v : E3) (g q) - c| := by
  obtain ⟨a, b, hgapA, hgapB, hcores⟩ := exists_terminal_slab_avoiding_inserted_caps data hg
  let R := min (data.ends.lowerCut - a) (b - data.ends.upperCut) / 2
  have hR : 0 < R := half_pos (lt_min (by linarith) (by linarith))
  have hRl : R < data.ends.lowerCut - a := by
    dsimp [R]
    linarith [min_le_left (data.ends.lowerCut - a) (b - data.ends.upperCut)]
  have hRu : R < b - data.ends.upperCut := by
    dsimp [R]
    linarith [min_le_right (data.ends.lowerCut - a) (b - data.ends.upperCut)]
  refine ⟨R, hR, ?_⟩
  intro c hc D hD q hq
  have hdeep := hcores D hD q hq
  rcases hc with rfl | rfl <;> rcases hdeep with hdeep | hdeep
  all_goals linarith [data.ends.cuts_lt,
    le_abs_self (inner Real (M.v : E3) (g q) - data.ends.lowerCut),
    neg_le_abs (inner Real (M.v : E3) (g q) - data.ends.lowerCut),
    le_abs_self (inner Real (M.v : E3) (g q) - data.ends.upperCut),
    neg_le_abs (inner Real (M.v : E3) (g q) - data.ends.upperCut)]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
