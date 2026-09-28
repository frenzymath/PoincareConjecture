import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.HomotopyToAffine
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.InjectiveFundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

set_option autoImplicit false

open Set Topology CategoryTheory

namespace PoincareConjecture.M76.LinearTorus

private theorem injective_fundamentalGroup_map_of_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (hf : Function.Injective (FundamentalGroup.map f x)) :
    Function.Injective (FundamentalGroup.map g x) := by
  let N := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  intro u v huv
  apply hf
  apply (cancel_mono (N.app ⟨x⟩)).mp
  exact (N.naturality u).trans ((congrArg (fun q => N.app ⟨x⟩ ≫ q) huv).trans
    (N.naturality v).symm)

theorem isCoveringMap_affineIntegerMatrixMap (p : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hp : 0 < p) (hA : A.det ≠ 0)
    (c : AddCircle p × AddCircle p) : IsCoveringMap (affineIntegerMatrixMap p A c) :=
  (isCoveringMap_integerMatrixMap p A hp hA).homeomorph_comp (Homeomorph.addLeft c)

theorem exists_homotopy_affine_covering (p : ℝ) (hp : 0 < p)
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p))
    (hf : Function.Injective (FundamentalGroup.map f 0)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A.det ≠ 0 ∧
      IsCoveringMap (affineIntegerMatrixMap p A (f 0)) ∧
      Nonempty (f.HomotopyRel (affineIntegerMatrixMap p A (f 0)) {0}) := by
  obtain ⟨A, ⟨H⟩⟩ := exists_homotopy_affineIntegerMatrixMap p f
  have hinj := injective_fundamentalGroup_map_of_homotopy H.toHomotopy 0 hf
  have hA := det_ne_zero_of_affine_fundamentalGroup_map_injective p A hp (f 0) hinj
  exact ⟨A, hA, isCoveringMap_affineIntegerMatrixMap p A hp hA (f 0), ⟨H⟩⟩

theorem exists_homotopy_coveringMap (p : ℝ) (hp : 0 < p)
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p))
    (hf : Function.Injective (FundamentalGroup.map f 0)) :
    ∃ g : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p),
      IsCoveringMap g ∧ Nonempty (f.HomotopyRel g {0}) := by
  obtain ⟨A, _, hcover, H⟩ := exists_homotopy_affine_covering p hp f hf
  exact ⟨affineIntegerMatrixMap p A (f 0), hcover, H⟩

end PoincareConjecture.M76.LinearTorus
