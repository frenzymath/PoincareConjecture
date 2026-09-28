import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightReversalData

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem SurgeryCapTag.reverseHeight_spec
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) :
    let C' : SurgeryCapTag psi (-u) := C.reverseHeight
    C'.profile = C.profile ∧
    C'.cutHeight = -C.cutHeight ∧
    C'.removal = C.removal ∧
    C'.scale = C.scale ∧
    C'.sign = -C.sign ∧
    C'.sourceChart = C.sourceChart ∧
    C'.overlapWidth = C.overlapWidth ∧
    C'.flatChart = C.flatChart ∧
    C'.beta = -C.beta ∧
    C'.collarWidth = C.collarWidth ∧
    (∀ p : E2 × ℝ, C'.tube p = C.tube (p.1, -p.2)) ∧
    (∀ y : E3, C'.tube.symm y =
      ((C.tube.symm y).1, -(C.tube.symm y).2)) ∧
    C'.tube.source = {p : E2 × ℝ | (p.1, -p.2) ∈ C.tube.source} ∧
    C'.tube.target = C.tube.target ∧
    (∀ q : UnitTwoSphere,
      C'.profile.capMap C'.tube C'.cutHeight C'.sign C'.removal C'.scale q =
        C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) ∧
    C'.sourceCap = C.sourceCap ∧
    C'.sourceSeam = C.sourceSeam ∧
    C'.cap = C.cap ∧
    C'.seam = C.seam ∧
    C'.cutHeight + C'.sign * C'.removal =
      -(C.cutHeight + C.sign * C.removal) := by
  dsimp only
  obtain ⟨hforward, hinverse, hsource, htarget⟩ := C.reverseHeight_tube
  obtain ⟨hsourceCap, hsourceSeam, hcap, hseam⟩ := C.reverseHeight_sets
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hforward, hinverse, hsource, htarget, ?_, hsourceCap, hsourceSeam, hcap, hseam, ?_⟩
  · intro q
    change C.tube ((C.profile.model q).1,
      -(-C.cutHeight + -C.sign * (C.removal + C.scale * (C.profile.model q).2))) =
        C.tube ((C.profile.model q).1,
          C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2))
    congr 1
    apply Prod.ext
    · rfl
    · ring
  · change -C.cutHeight + -C.sign * C.removal =
      -(C.cutHeight + C.sign * C.removal)
    ring

end PoincareConjecture.M25.Topology3D
