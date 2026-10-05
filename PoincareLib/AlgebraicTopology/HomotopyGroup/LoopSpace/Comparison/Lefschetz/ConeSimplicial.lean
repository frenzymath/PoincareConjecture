import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedNerve
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The literal extra degeneracy of a nerve cone

Prepending a selected least vertex gives the standard cone extra
degeneracy. Keeping a separate constant fiber coordinate gives the
augmentation needed for a covering of a contractible cone neighborhood.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial MonoidalCategory

universe u

namespace PoincareMT.Proofs.M59

variable {J : Type u} [PartialOrder J]
  (s : Finset J) (v : J) (hv : v ∈ s) (hmin : ∀ j ∈ s, v ≤ j)

/-- Prepend the actual least vertex to a simplex of the selected nerve.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def nerveConePrepend {n : ℕ} (z : (supportedNerve s).toSSet _⦋n⦌) :
    (supportedNerve s).toSSet _⦋n + 1⦌ := by
  refine ⟨z.val.precomp (homOfLE (hmin _ (z.property 0))), ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact hv
  | succ i => exact z.property i

/-- The zeroth face of the cone is the original simplex.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem nerveConePrepend_face_zero {n : ℕ} (z : (supportedNerve s).toSSet _⦋n⦌) :
    (supportedNerve s).toSSet.δ 0 (nerveConePrepend s v hv hmin z) = z := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- The remaining faces commute with cone formation.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem nerveConePrepend_face_succ {n : ℕ} (i : Fin (n + 2))
    (z : (supportedNerve s).toSSet _⦋n + 1⦌) :
    (supportedNerve s).toSSet.δ i.succ (nerveConePrepend s v hv hmin z) =
      nerveConePrepend s v hv hmin ((supportedNerve s).toSSet.δ i z) := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext j
  change ComposableArrows.Precomp.obj z.val v (i.succ.succAbove j) =
    ComposableArrows.Precomp.obj ((nerve J).δ i z.val) v j
  cases j using Fin.cases with
  | zero => rw [Fin.succ_succAbove_zero]; rfl
  | succ j => rw [Fin.succ_succAbove_succ]; rfl

/-- Degeneracies commute with cone formation after shifting the index.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem nerveConePrepend_degeneracy_succ {n : ℕ} (i : Fin (n + 1))
    (z : (supportedNerve s).toSSet _⦋n⦌) :
    (supportedNerve s).toSSet.σ i.succ (nerveConePrepend s v hv hmin z) =
      nerveConePrepend s v hv hmin ((supportedNerve s).toSSet.σ i z) := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext j
  change ComposableArrows.Precomp.obj z.val v (i.succ.predAbove j) =
    ComposableArrows.Precomp.obj ((nerve J).σ i z.val) v j
  cases j using Fin.cases with
  | zero => rw [Fin.predAbove_right_zero]; rfl
  | succ j => rw [Fin.succ_predAbove_succ]; rfl

/-- The retained least vertex as an actual zero-simplex of the cone.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def nerveConeVertex : (supportedNerve s).toSSet _⦋0⦌ :=
  ⟨ComposableArrows.mk₀ v, fun _ => hv⟩

/-- The final vertex of a coned zero-simplex is the retained cone point.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem nerveConePrepend_face_one (z : (supportedNerve s).toSSet _⦋0⦌) :
    (supportedNerve s).toSSet.δ 1 (nerveConePrepend s v hv hmin z) =
      nerveConeVertex s v hv := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

/-- Copies of the actual nerve cone augmented to their retained fiber
labels. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def fiberConeAugmented (F : Type u) : SimplicialObject.Augmented (Type u) where
  left := (SimplicialObject.const (Type u)).obj F ⊗ (supportedNerve s).toSSet
  right := F
  hom := { app _ := ↾Prod.fst }

/-- The fiber-indexed cone has a literal extra degeneracy and therefore
its augmented integral chains contract onto the fiber in degree zero.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def fiberConeExtraDegeneracy (F : Type u) :
    SimplicialObject.Augmented.ExtraDegeneracy (fiberConeAugmented s F) where
  s' := ↾fun a => (a, nerveConeVertex s v hv)
  s _ := ↾fun z => (z.1, nerveConePrepend s v hv hmin z.2)
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext rfl (nerveConePrepend_face_one s v hv hmin z.2)
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext rfl (nerveConePrepend_face_zero s v hv hmin z.2)
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext rfl (nerveConePrepend_face_succ s v hv hmin i z.2)
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext rfl (nerveConePrepend_degeneracy_succ s v hv hmin i z.2)

end PoincareMT.Proofs.M59
