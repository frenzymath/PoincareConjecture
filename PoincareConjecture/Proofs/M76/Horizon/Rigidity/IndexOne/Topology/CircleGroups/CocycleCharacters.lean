import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CocyclePathIntegral
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleConnected
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCocycleOfClosed
import PoincareConjecture.Proofs.M54.Mathlib.PathSubdivision

set_option autoImplicit false

open Set

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

noncomputable def quotientValue (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path.Homotopic.Quotient x y) : ZMod 2 :=
  Quotient.lift c.pathValue (fun _ _ h => c.pathValue_eq_of_homotopic h) p

@[simp] theorem quotientValue_mk (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path x y) :
    c.quotientValue (Path.Homotopic.Quotient.mk p) = c.pathValue p := rfl

@[simp] theorem quotientValue_refl (c : A.ModTwoEdgeCocycle) (x : A.barycentricSpace) :
    c.quotientValue (Path.Homotopic.Quotient.refl x) = 0 := c.pathValue_refl x

theorem quotientValue_trans (c : A.ModTwoEdgeCocycle)
    {x y z : A.barycentricSpace} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) :
    c.quotientValue (p.trans q) = c.quotientValue p + c.quotientValue q := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q => exact c.pathValue_trans p q

noncomputable def loopCharacter (c : A.ModTwoEdgeCocycle) (x : A.barycentricSpace) :
    FundamentalGroup A.barycentricSpace x →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd (c.quotientValue p)
  map_one' := congrArg Multiplicative.ofAdd (c.quotientValue_refl x)
  map_mul' p q := by
    change c.quotientValue (q.trans p) = c.quotientValue p + c.quotientValue q
    rw [c.quotientValue_trans, add_comm]

theorem pathValue_of_mem_openVertexStar (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path x y) (i : ι)
    (hp : ∀ t, p t ∈ A.openVertexStar i) :
    c.pathValue p = c.value i (c.bundle.indexAt y) - c.value i (c.bundle.indexAt x) := by
  have hx : x ∈ A.openVertexStar i := by simpa using hp 0
  have hy : y ∈ A.openVertexStar i := by simpa using hp 1
  let P : Path (⟨x, hx⟩ : A.openVertexStar i) ⟨y, hy⟩ :=
    ⟨⟨fun t => ⟨p t, hp t⟩, p.continuous.subtype_mk _⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  have h := c.pathValue_of_lift p (P.map (c.sheet i 0).continuous) (fun _ => rfl)
  change c.pathValue p = (0 + c.value i (c.bundle.indexAt y)) -
    (0 + c.value i (c.bundle.indexAt x)) at h
  simpa only [zero_add] using h

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

omit [Fintype ι] in
theorem edgeValue_add (z w : Edge A → ZMod 2) (i j : ι) :
    edgeValue A (z + w) i j = edgeValue A z i j + edgeValue A w i j := by
  classical
  unfold edgeValue
  split_ifs <;> simp

theorem quotientValue_cocycleOfClosed_add
    (z w : LinearMap.ker (edgeCoboundary A))
    {x y : A.barycentricSpace} (p : Path.Homotopic.Quotient x y) :
    (cocycleOfClosed A (z + w) (z + w).property).quotientValue p =
      (cocycleOfClosed A z z.property).quotientValue p +
        (cocycleOfClosed A w w.property).quotientValue p := by
  refine Path.homotopicQuotient_induction_of_open_cover A.openVertexStar
    A.isOpen_openVertexStar (Set.iUnion_eq_univ_iff.mpr A.exists_mem_openVertexStar)
    (fun {_ _} q =>
      (cocycleOfClosed A (z + w) (z + w).property).quotientValue q =
        (cocycleOfClosed A z z.property).quotientValue q +
          (cocycleOfClosed A w w.property).quotientValue q) ?_ ?_ ?_ p
  · intro a
    simp
  · intro a b c p q hp hq
    simp only [ModTwoEdgeCocycle.quotientValue_trans, hp, hq]
    abel
  · intro a b p i hp
    simp only [ModTwoEdgeCocycle.quotientValue_mk,
      ModTwoEdgeCocycle.pathValue_of_mem_openVertexStar _ p i hp]
    change edgeValue A ((z : Edge A → ZMod 2) + w) i _ -
        edgeValue A ((z : Edge A → ZMod 2) + w) i _ =
      (edgeValue A z i _ - edgeValue A z i _) +
        (edgeValue A w i _ - edgeValue A w i _)
    rw [edgeValue_add, edgeValue_add]
    dsimp only [ModTwoEdgeCocycle.bundle]
    abel

noncomputable def closedCochainEvaluation
    {x y : A.barycentricSpace} (p : Path.Homotopic.Quotient x y) :
    LinearMap.ker (edgeCoboundary A) →ₗ[ZMod 2] ZMod 2 where
  toFun z := (cocycleOfClosed A z z.property).quotientValue p
  map_add' z w := quotientValue_cocycleOfClosed_add A z w p
  map_smul' a z := by
    have hzero : (cocycleOfClosed A 0 (LinearMap.map_zero _)).quotientValue p = 0 := by
      have h := quotientValue_cocycleOfClosed_add A 0 0 p
      simpa only [Submodule.coe_zero, zero_add, CharTwo.add_self_eq_zero] using h
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa only [zero_smul, RingHom.id_apply, Submodule.coe_zero] using hzero
    · simp only [one_smul, RingHom.id_apply]

end PreAbstractSimplicialComplex.ModTwoCochains
