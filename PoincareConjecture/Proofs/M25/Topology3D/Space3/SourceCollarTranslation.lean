import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceTubeChart











set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D


noncomputable def circleTimeTranslation (t : ℝ) :
    Diffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (UnitCircle × ℝ) (UnitCircle × ℝ) ∞ where
  toEquiv := {
    toFun := fun p => (p.1, t + p.2)
    invFun := fun p => (p.1, p.2 - t)
    left_inv := fun p => Prod.ext rfl (by dsimp; ring)
    right_inv := fun p => Prod.ext rfl (by dsimp; ring) }
  contMDiff_toFun := contMDiff_fst.prodMk
    ((contDiff_const.add contDiff_id).contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_snd)



theorem exists_centered_source_collar
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    (t d : ℝ) (hs : Q.source = univ ×ˢ Ioo (t - d) (t + d)) :
    ∃ C : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere,
      C.source = univ ×ˢ Ioo (-d) d ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ C.symm C.target ∧
      ∀ p : UnitCircle × ℝ, C p = Q (p.1, t + p.2) := by
  let A := circleTimeTranslation t
  let C := A.toHomeomorph.toOpenPartialHomeomorph.trans Q
  have hCs : C.source = univ ×ˢ Ioo (-d) d := by
    ext p
    change (p ∈ (univ : Set (UnitCircle × ℝ)) ∧ A p ∈ Q.source) ↔
      p ∈ (univ : Set UnitCircle) ×ˢ Ioo (-d) d
    rw [hs]
    change (True ∧ True ∧ t - d < t + p.2 ∧ t + p.2 < t + d) ↔
      True ∧ -d < p.2 ∧ p.2 < d
    constructor <;> rintro ⟨_, h⟩
    · exact ⟨trivial, by linarith [h.2.1], by linarith [h.2.2]⟩
    · exact ⟨trivial, trivial, by linarith [h.1], by linarith [h.2]⟩
  refine ⟨C, hCs, ?_, ?_, fun _ => rfl⟩
  · exact hQ.comp A.contMDiff_toFun.contMDiffOn (fun _ hp => hp.2)
  · exact A.contMDiff_invFun.comp_contMDiffOn (hQi.mono inter_subset_left)

end PoincareConjecture.M25.Topology3D
