import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceTubeChart

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def circleTimeReflection :
    Diffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (UnitCircle × ℝ) (UnitCircle × ℝ) ∞ where
  toEquiv := {
    toFun := fun p => (p.1, -p.2)
    invFun := fun p => (p.1, -p.2)
    left_inv := fun p => Prod.ext rfl (neg_neg p.2)
    right_inv := fun p => Prod.ext rfl (neg_neg p.2) }
  contMDiff_toFun := contMDiff_fst.prodMk
    (contDiff_id.neg.contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (contDiff_id.neg.contMDiff.comp contMDiff_snd)

theorem exists_reflected_source_collar
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    (d : ℝ) (hs : Q.source = univ ×ˢ Ioo (-d) d) :
    ∃ C : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere,
      C.source = univ ×ˢ Ioo (-d) d ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ C.symm C.target ∧
      ∀ p : UnitCircle × ℝ, C p = Q (p.1, -p.2) := by
  let A := circleTimeReflection
  let C := A.toHomeomorph.toOpenPartialHomeomorph.trans Q
  have hCs : C.source = univ ×ˢ Ioo (-d) d := by
    ext p
    change (p ∈ (univ : Set (UnitCircle × ℝ)) ∧ A p ∈ Q.source) ↔
      p ∈ (univ : Set UnitCircle) ×ˢ Ioo (-d) d
    rw [hs]
    change (True ∧ True ∧ -d < -p.2 ∧ -p.2 < d) ↔
      True ∧ -d < p.2 ∧ p.2 < d
    constructor
    · rintro ⟨_, _, hlo, hhi⟩
      exact ⟨trivial, by linarith, by linarith⟩
    · rintro ⟨_, hlo, hhi⟩
      exact ⟨trivial, trivial, by linarith, by linarith⟩
  refine ⟨C, hCs, ?_, ?_, fun _ => rfl⟩
  · exact hQ.comp A.contMDiff_toFun.contMDiffOn (fun _ hp => hp.2)
  · exact A.contMDiff_invFun.comp_contMDiffOn (hQi.mono inter_subset_left)

end PoincareConjecture.M25.Topology3D
