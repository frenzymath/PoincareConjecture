import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem image_slice_eq_height_level
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (v : E3)
    (hF : ∀ y, F y 2 = inner Real v y) (k : S2 → E3) (z : Real) :
    (fun x => Saddle.toE3 x z) '' {x | Saddle.toE3 x z ∈ F '' range k} =
      (F ∘ k) '' {q | inner Real v (k q) = z} := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨_, ⟨q, rfl⟩, heq⟩, rfl⟩
    refine ⟨q, ?_, heq⟩
    exact (hF (k q)).symm.trans (congrArg (fun y : E3 => y 2) heq)
  · rintro _ ⟨q, hq, rfl⟩
    have hh : F (k q) 2 = z := (hF (k q)).trans hq
    have heq : Saddle.toE3 (Saddle.toE2 (F (k q))) z = F (k q) := by
      ext i
      fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hh]
    refine ⟨Saddle.toE2 (F (k q)), ?_, heq⟩
    change Saddle.toE3 (Saddle.toE2 (F (k q))) z ∈ F '' range k
    rw [heq]
    exact mem_image_of_mem F (mem_range_self q)

private theorem preconnected_slice_iff_height_level
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (v : E3)
    (hF : ∀ y, F y 2 = inner Real v y) (k : S2 → E3)
    (hk : Topology.IsEmbedding k) (z : Real) :
    IsPreconnected {x | Saddle.toE3 x z ∈ F '' range k} ↔
      IsPreconnected {q | inner Real v (k q) = z} := by
  have hleft : Function.LeftInverse Saddle.toE2 (fun x => Saddle.toE3 x z) := by
    intro x
    ext i
    fin_cases i <;> rfl
  have hplane : Topology.IsEmbedding (fun x => Saddle.toE3 x z) :=
    hleft.isEmbedding (by unfold Saddle.toE2; fun_prop)
      (by unfold Saddle.toE3; fun_prop)
  have heq := hplane.isInducing.isPreconnected_image
    (s := {x | Saddle.toE3 x z ∈ F '' range k})
  rw [image_slice_eq_height_level F v hF k z] at heq
  exact heq.symm.trans (F.toHomeomorph.isEmbedding.comp hk).isInducing.isPreconnected_image

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem flatten_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    d.flatten y 2 = inner Real (M.v : E3) y :=
  (d.frame_height (d.D y)).trans (d.D_height y)


theorem actual_slice_image_eq_height_level
    (d : TerminalSaddleGeometry M P p e) (z : Real) :
    (fun x => Saddle.toE3 x z) '' d.A z =
      (d.flatten ∘ g) '' {q | inner Real (M.v : E3) (g q) = z} :=
  image_slice_eq_height_level d.flatten M.v (flatten_height d) g z


theorem model_slice_image_eq_height_level
    (d : TerminalSaddleGeometry M P p e) (z : Real) :
    (fun x => Saddle.toE3 x z) '' d.B z =
      (fun q : S2 => d.flatten (d.filledModel q)) ''
        {q : S2 | inner Real (M.v : E3) (d.filledModel q) = z} := by
  have hr : range (fun q : S2 => d.filledModel q) =
      d.filledModel '' sphere (0 : E3) 1 := by
    exact (image_eq_range _ _).symm
  simpa only [hr, TerminalSaddleGeometry.B, Function.comp_def] using
    image_slice_eq_height_level d.flatten M.v (flatten_height d)
    (fun q : S2 => d.filledModel q) z


theorem actual_slice_preconnected_iff
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e) (z : Real) :
    IsPreconnected (d.A z) ↔
      IsPreconnected {q : S2 | inner Real (M.v : E3) (g q) = z} :=
  preconnected_slice_iff_height_level d.flatten M.v (flatten_height d) g
    (M.tree.embedding_of_mem_leaves hg).isEmbedding z


theorem model_slice_preconnected_iff
    (d : TerminalSaddleGeometry M P p e) (z : Real) :
    IsPreconnected (d.B z) ↔
      IsPreconnected {q : S2 | inner Real (M.v : E3) (d.filledModel q) = z} := by
  have hr : range (fun q : S2 => d.filledModel q) =
      d.filledModel '' sphere (0 : E3) 1 := (image_eq_range _ _).symm
  simpa only [hr, TerminalSaddleGeometry.B] using preconnected_slice_iff_height_level d.flatten M.v
    (flatten_height d) (fun q : S2 => d.filledModel q)
    (d.filledModel.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal) z


theorem actual_lower_slice_preconnected_of_one_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    IsPreconnected (d.A d.ends.lowerCut) := by
  obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hcount
  have hlevel : {q : S2 | inner Real (M.v : E3) (g q) = d.ends.lowerCut} =
      range (d.ends.lowerCutCircle i) := by
    rw [← d.ends.iUnion_range_lowerCutCircle]
    apply Subset.antisymm
    · rintro q ⟨_, ⟨j, rfl⟩, hq⟩
      rwa [hi j] at hq
    · intro q hq
      exact mem_iUnion_of_mem i hq
  apply (actual_slice_preconnected_iff hg d _).mpr
  rw [hlevel]
  let : ConnectedSpace (sphere (0 : E2) 1) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  exact (isConnected_range (d.ends.lowerCutCircle_geometry i).1.continuous).isPreconnected



theorem height_level_preconnected_iff_of_terminal_slice_matching
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e) (z : Real)
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (hQ : Q '' d.A z = d.B z) :
    IsPreconnected {q : S2 | inner Real (M.v : E3) (g q) = z} ↔
      IsPreconnected {q : S2 | inner Real (M.v : E3) (d.filledModel q) = z} := by
  have h := Q.toHomeomorph.isInducing.isPreconnected_image (s := d.A z)
  change IsPreconnected (Q '' d.A z) ↔ IsPreconnected (d.A z) at h
  rw [hQ] at h
  exact (actual_slice_preconnected_iff hg d z).symm.trans
    (h.symm.trans (model_slice_preconnected_iff d z))



theorem no_terminal_slice_matching_of_height_level_mismatch
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e) (z : Real)
    (hmismatch : ¬ (IsPreconnected {q : S2 | inner Real (M.v : E3) (g q) = z} ↔
      IsPreconnected {q : S2 | inner Real (M.v : E3) (d.filledModel q) = z})) :
    ¬ ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞, Q '' d.A z = d.B z := by
  rintro ⟨Q, hQ⟩
  exact hmismatch (height_level_preconnected_iff_of_terminal_slice_matching hg d z Q hQ)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
