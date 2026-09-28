import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.OrientationChoice
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.AnnularEnds



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel SphereSurgeryCoreCap
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem lower_level_connected_of_one_annular_end
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C) (hcount : Nat.card A.LowerCutIndex = 1) :
    IsConnected {q : S2 | inner Real v (g q) = A.lowerCut} := by
  obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hcount
  have hlevel : {q : S2 | inner Real v (g q) = A.lowerCut} =
      range (A.lowerCutCircle i) := by
    rw [← A.iUnion_range_lowerCutCircle]
    apply Subset.antisymm
    · rintro q ⟨_, ⟨j, rfl⟩, hq⟩
      rwa [hi j] at hq
    · intro q hq
      exact mem_iUnion_of_mem i hq
  rw [hlevel]
  let : ConnectedSpace (sphere (0 : E2) 1) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  exact isConnected_range (A.lowerCutCircle_geometry i).1.continuous

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem one_lower_end_of_one_lower_annular_family
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    {B : Set Real} (A : AnnularEndFamily (M.v : E3) g B P.core)
    (hlow : A.lowerCut < inner Real (M.v : E3) (g p))
    (hupp : inner Real (M.v : E3) (g p) < A.upperCut)
    (hcount : Nat.card A.LowerCutIndex = 1) : Nat.card d.ends.LowerCutIndex = 1 := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp (M.tree.embedding_of_mem_leaves hg).contMDiff
  have hdlo : d.ends.lowerCut < h p := by rw [d.lowerCut_eq]; dsimp [h]; linarith [d.eta_pos]
  have hdhi : h p < d.ends.upperCut := by rw [d.upperCut_eq]; dsimp [h]; linarith [d.eta_pos]
  have hregular {B' : Set Real} (A' : AnnularEndFamily (M.v : E3) g B' P.core)
      (hupper : h p < A'.upperCut) {b : Real} (hb : b < h p)
      (q : S2) (hq : h q ∈ Icc A'.lowerCut b) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hc
    have hqcore : q ∈ P.core := A'.physical_middle_band_subset_core
      ⟨hq.1, by change h q ≤ A'.upperCut; linarith [hq.2]⟩
    have hqp := hunique q hqcore hc
    subst q
    exact hb.not_ge hq.2
  apply d.ends.card_lowerCutIndex_eq_one_of_isConnected
  have hbottom := lower_level_connected_of_one_annular_end A hcount
  rcases le_total A.lowerCut d.ends.lowerCut with hle | hle
  · exact connected_top_of_regular_band hh hle (hregular A hupp hdlo) hbottom
  · have hnreg (q : S2) (hq : -h q ∈ Icc (-A.lowerCut) (-d.ends.lowerCut)) :
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => -h q) q ≠ 0 := by
      change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q ≠ 0
      rw [mfderiv_neg]
      exact neg_ne_zero.mpr (hregular d.ends hdhi hlow q
        ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have hn := connected_top_of_regular_band hh.neg (neg_le_neg hle) hnreg
      (show IsConnected ((fun q => -h q) ⁻¹' {-A.lowerCut}) by
        simpa only [preimage, mem_singleton_iff, neg_inj] using hbottom)
    simpa only [preimage, mem_singleton_iff, neg_inj] using hn



theorem no_terminal_matching_choice_of_one_lower_annular_family
    (hg : g ∈ M.tree.leaves)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {B : Set Real} (A : AnnularEndFamily (M.v : E3) g B P.core)
    (hlow : A.lowerCut < inner Real (M.v : E3) (g p))
    (hupp : inner Real (M.v : E3) (g p) < A.upperCut)
    (hcount : Nat.card A.LowerCutIndex = 1) :
    ¬ ∃ data : TerminalSaddleData M P p e,
      ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ z ∈ data.toTerminalSaddleGeometry.I,
          Q z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z := by
  intro hmatch
  obtain ⟨data, Q, hQ⟩ := hmatch
  have hcount' := one_lower_end_of_one_lower_annular_family hg
    data.toTerminalSaddleGeometry hunique A hlow hupp hcount
  exact no_terminal_matching_choice_of_one_lower_end hg data.toTerminalSaddleGeometry
    hunique hform hcount' ⟨data, Q, hQ⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
