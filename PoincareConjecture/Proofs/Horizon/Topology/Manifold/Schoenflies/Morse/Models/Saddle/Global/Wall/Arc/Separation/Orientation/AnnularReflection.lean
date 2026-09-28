import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Reflection



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IA" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private def negateTime : Real ≃ₘ[Real] Real where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

private def annularReflection : Diffeomorph IA IA (S1 × Real) (S1 × Real) ∞ :=
  (Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr negateTime

def reflectedAnnularChart (T : OpenPartialHomeomorph (S1 × Real) S2) :
    OpenPartialHomeomorph (S1 × Real) S2 :=
  annularReflection.toHomeomorph.toOpenPartialHomeomorph.trans T

@[simp] theorem reflectedAnnularChart_apply (T : OpenPartialHomeomorph (S1 × Real) S2)
    (q : S1) (t : Real) : reflectedAnnularChart T (q,t) = T (q,-t) := rfl

@[simp] theorem reflectedAnnularChart_target (T : OpenPartialHomeomorph (S1 × Real) S2) :
    (reflectedAnnularChart T).target = T.target := by
  change T.target ∩ T.symm ⁻¹' (univ : Set (S1 × Real)) = T.target
  simp

theorem reflectedAnnularChart_source (T : OpenPartialHomeomorph (S1 × Real) S2)
    {a b : Real} (hT : T.source = univ ×ˢ Ioo a b) :
    (reflectedAnnularChart T).source = univ ×ˢ Ioo (-b) (-a) := by
  ext z
  change (z ∈ univ ∧ (z.1,-z.2) ∈ T.source) ↔ _
  rw [hT]
  simp only [mem_univ, mem_prod, mem_Ioo, true_and]
  constructor <;> intro hz <;> constructor <;> linarith [hz.1,hz.2]

theorem reflectedAnnularChart_smooth (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn IA (𝓡 2) ∞ T T.source) :
    ContMDiffOn IA (𝓡 2) ∞ (reflectedAnnularChart T) (reflectedAnnularChart T).source :=
  hT.comp annularReflection.contMDiff.contMDiffOn inter_subset_right

theorem reflectedAnnularChart_symm_smooth (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTi : ContMDiffOn (𝓡 2) IA ∞ T.symm T.target) :
    ContMDiffOn (𝓡 2) IA ∞ (reflectedAnnularChart T).symm (reflectedAnnularChart T).target :=
  annularReflection.symm.contMDiff.comp_contMDiffOn (hTi.mono inter_subset_left)

theorem reflectedAnnularChart_height {v : E3} {g : S2 → E3}
    (T : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real}
    (hheight : ∀ q t, t ∈ Ioo a b → inner Real v (g (T (q,t))) = t) :
    ∀ q t, t ∈ Ioo (-b) (-a) →
      inner Real (-v) (g (reflectedAnnularChart T (q,t))) = t := by
  intro q t ht
  rw [reflectedAnnularChart_apply, inner_neg_left,
    hheight q (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg]

end Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation
