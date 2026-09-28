import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup



set_option autoImplicit false
open CategoryTheory

namespace FundamentalGroup

theorem map_injective_of_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (hf : Function.Injective (map f x)) : Function.Injective (map g x) := by
  let T := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  intro a b hab
  apply hf
  change (FundamentalGroupoid.map f).map a = (FundamentalGroupoid.map f).map b
  apply (cancel_mono (T.app ⟨x⟩)).mp
  rw [T.naturality, T.naturality]
  exact congrArg (fun u => T.app ⟨x⟩ ≫ u) hab

end FundamentalGroup
