import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.CharacterKernel
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions











set_option autoImplicit false

namespace PoincareConjecture.M76

open Module

theorem exists_three_character_detectors
    {G : Type*} [Group G] (f : G →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) :
    ∃ g : Fin 3 → G, ∀ c : G →* Multiplicative (ZMod 2),
      (∀ i, c (g i) = 1) → ∀ q, c q = 1 := by
  classical
  let S : AddSubgroup (Fin 3 → ℤ) :=
    { carrier := {v | ∃ g, f g = Multiplicative.ofAdd v}
      zero_mem' := ⟨1, f.map_one⟩
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x * y, by rw [map_mul, hx, hy]; rfl⟩
      neg_mem' := by
        rintro a ⟨x, hx⟩
        exact ⟨x⁻¹, by rw [map_inv, hx]; rfl⟩ }
  let F : G →* Multiplicative S :=
    { toFun := fun g => Multiplicative.ofAdd ⟨Multiplicative.toAdd (f g), g, rfl⟩
      map_one' := Subtype.ext (congrArg Multiplicative.toAdd f.map_one)
      map_mul' := fun x y => Subtype.ext (congrArg Multiplicative.toAdd (f.map_mul x y)) }
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      apply hf
      exact congrArg (fun z : Multiplicative S => Multiplicative.ofAdd
        (Multiplicative.toAdd z).val) h
    · intro z
      obtain ⟨g, hg⟩ := (Multiplicative.toAdd z).property
      exact ⟨g, Subtype.ext (congrArg Multiplicative.toAdd hg)⟩
  let e := MulEquiv.ofBijective F hF
  obtain ⟨r, b⟩ := S.toIntSubmodule.basisOfPid (Pi.basisFun ℤ (Fin 3))
  have hr : r ≤ 3 := by
    have h := S.toIntSubmodule.finrank_le
    rw [finrank_eq_card_basis b] at h
    simpa using h
  let g : Fin 3 → G := fun i =>
    if h : i.val < r then e.symm (Multiplicative.ofAdd (b ⟨i.val, h⟩)) else 1
  refine ⟨g, ?_⟩
  intro c hc q
  let a : S →+ ZMod 2 :=
    { toFun := fun z => Multiplicative.toAdd (c (e.symm (Multiplicative.ofAdd z)))
      map_zero' := by change c (e.symm 1) = 1; simp
      map_add' := by
        intro x y
        change c (e.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
        rw [map_mul, map_mul]
        rfl }
  have ha : a.toIntLinearMap = 0 := by
    apply b.ext
    intro i
    have hi : i.val < 3 := lt_of_lt_of_le i.isLt hr
    have h := hc ⟨i.val, hi⟩
    change Multiplicative.toAdd (c (e.symm (Multiplicative.ofAdd (b i)))) = 0
    have h' : c (e.symm (Multiplicative.ofAdd (b i))) = 1 := by
      simpa only [g, dif_pos i.isLt] using h
    exact congrArg Multiplicative.toAdd h'
  have hq := congrArg (fun l : S →ₗ[ℤ] ZMod 2 => l (Multiplicative.toAdd (e q))) ha
  change c (e.symm (e q)) = 1 at hq
  simpa using hq

end PoincareConjecture.M76

namespace PreAbstractSimplicialComplex.ModTwoCochains



theorem exists_three_coordinate_evaluation_of_injective
    {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)
    [PathConnectedSpace A.barycentricSpace] (hvertex : ∀ i : ι, {i} ∈ A.faces)
    (x : A.barycentricSpace)
    (f : FundamentalGroup A.barycentricSpace x →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) :
    ∃ (eval : LinearMap.ker (edgeCoboundary A) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (T : LinearMap.ker eval →ₗ[ZMod 2] LinearMap.range (vertexCoboundary A)),
      Function.Injective T := by
  classical
  obtain ⟨g, hg⟩ := PoincareConjecture.M76.exists_three_character_detectors f hf
  let eval := LinearMap.pi (fun i => closedCochainEvaluation A (g i))
  have hker (z : LinearMap.ker (edgeCoboundary A)) (hz : eval z = 0) :
      (z : Edge A → ZMod 2) ∈ LinearMap.range (vertexCoboundary A) := by
    apply mem_range_vertexCoboundary_of_coboundary A z z.property
    let c := cocycleOfClosed A z z.property
    apply c.isCoboundary_of_loopCharacter_eq_one hvertex x
    apply hg (c.loopCharacter x)
    intro i
    exact congrArg Multiplicative.ofAdd (congrFun hz i)
  let T : LinearMap.ker eval →ₗ[ZMod 2] LinearMap.range (vertexCoboundary A) :=
    { toFun := fun z => ⟨z.val.val, hker z.val z.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨eval, T, ?_⟩
  intro z w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : LinearMap.range (vertexCoboundary A) => t.val) h

end PreAbstractSimplicialComplex.ModTwoCochains
