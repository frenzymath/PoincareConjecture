import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RelativeTriangleChains
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedIncidenceRanks

set_option autoImplicit false
open scoped BigOperators
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι β : Type*} [Fintype ι] [Fintype β]
  (A : PreAbstractSimplicialComplex ι)

noncomputable def boundaryCycleMap (B : β → Edge A → Prop) :
    (β → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Edge A → ZMod 2) :=
  ∑ i, (LinearMap.proj i).smulRight (markedEdgeChain A (B i))

open Classical in
theorem boundaryCycleMap_apply (B : β → Edge A → Prop) (r : β → ZMod 2) :
    boundaryCycleMap A B r = ∑ i, r i • markedEdgeChain A (B i) := by
  simp [boundaryCycleMap]

open Classical in
theorem boundaryCycleMap_coordinate
    (B : β → Edge A → Prop)
    (hdis : ∀ i j, i ≠ j → ∀ e, B i e → ¬ B j e)
    (r : β → ZMod 2) {i : β} {e : Edge A} (he : B i e) :
    boundaryCycleMap A B r (Pi.single e 1) = r i := by
  classical
  rw [boundaryCycleMap_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, markedEdgeChain_single]
  rw [Finset.sum_eq_single i]
  · simp only [if_pos he, mul_one]
  · intro j _ hji
    simp only [if_neg (hdis i j hji.symm e he), mul_zero]
  · simp

open Classical in
theorem boundaryCycleMap_injective
    (B : β → Edge A → Prop)
    (hdis : ∀ i j, i ≠ j → ∀ e, B i e → ¬ B j e)
    (hne : ∀ i, ∃ e, B i e) : Function.Injective (boundaryCycleMap A B) := by
  intro r s hrs
  funext i
  obtain ⟨e, he⟩ := hne i
  exact (boundaryCycleMap_coordinate A B hdis r he).symm.trans
    ((congrArg (fun c ↦ c (Pi.single e 1)) hrs).trans
      (boundaryCycleMap_coordinate A B hdis s he))

open Classical in
theorem boundaryCycle_rank_bound [Nonempty β]
    (B : β → Edge A → Prop)
    (hdis : ∀ i j, i ≠ j → ∀ e, B i e → ¬ B j e)
    (hne : ∀ i, ∃ e, B i e)
    (hcycle : ∀ i, (vertexCoboundary A).dualMap (markedEdgeChain A (B i)) = 0)
    (hcofaces : ∀ e : Edge A,
      (triangleCofaces A e).card = if ∃ i, B i e then 1 else 2)
    (htri : (triangleGraph A).Connected) :
    Nat.card β + Nat.card (Triangle A) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary A).dualMap) + 1 := by
  classical
  let W := LinearMap.range (boundaryCycleMap A B)
  let T := LinearMap.range (edgeCoboundary A).dualMap
  let Z := LinearMap.ker (vertexCoboundary A).dualMap
  have hW : Module.finrank (ZMod 2) W = Nat.card β := by
    have h := LinearMap.finrank_range_of_inj (boundaryCycleMap_injective A B hdis hne)
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h
  have hone : ∃ e : Edge A, (triangleCofaces A e).card = 1 := by
    obtain ⟨i⟩ := ‹Nonempty β›
    obtain ⟨e, he⟩ := hne i
    exact ⟨e, by rw [hcofaces, if_pos ⟨i, he⟩]⟩
  have hle (e : Edge A) : (triangleCofaces A e).card ≤ 2 := by
    rw [hcofaces]
    split_ifs <;> norm_num
  have hT : Module.finrank (ZMod 2) T = Nat.card (Triangle A) := by
    have h := (edgeCoboundary A).dualMap.finrank_range_add_finrank_ker
    rw [finrank_boundary2_ker_of_one_coface A hle htri.preconnected hone,
      add_zero, Subspace.dual_finrank_eq, Module.finrank_pi] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hInf : (W ⊓ T : Submodule (ZMod 2) _) ≤
      Submodule.span (ZMod 2) {markedEdgeChain A (fun e ↦ ∃ i, B i e)} := by
    rintro z ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
    obtain ⟨a, _, ha⟩ := exists_scalar_totalTriangle_of_relative_boundary A
      (fun e ↦ ∃ i, B i e) (fun e ↦ by
        by_cases he : ∃ i, B i e <;> simpa only [he, ite_true, ite_false] using hcofaces e)
      htri c (by
        intro e he
        rw [hc, ← hr, boundaryCycleMap_apply, LinearMap.sum_apply]
        apply Finset.sum_eq_zero
        intro i _
        simp only [LinearMap.smul_apply, smul_eq_mul, markedEdgeChain_single,
          if_neg (fun hi ↦ he ⟨i, hi⟩), mul_zero])
    rw [← hc, ha]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))
  have hInfRank : Module.finrank (ZMod 2) (W ⊓ T : Submodule (ZMod 2) _) ≤ 1 :=
    (Submodule.finrank_mono hInf).trans (by
      simpa using finrank_span_le_card
        ({markedEdgeChain A (fun e ↦ ∃ i, B i e)} : Set _))
  have hWZ : W ≤ Z := by
    rintro _ ⟨r, rfl⟩
    change (vertexCoboundary A).dualMap (boundaryCycleMap A B r) = 0
    rw [boundaryCycleMap_apply, map_sum]
    simp only [map_smul, hcycle, smul_zero, Finset.sum_const_zero]
  have hTZ : T ≤ Z := by
    rintro _ ⟨c, rfl⟩
    apply LinearMap.ext
    intro v
    change c (edgeCoboundary A (vertexCoboundary A v)) = 0
    rw [edgeCoboundary_vertexCoboundary, map_zero]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W T
  have hsup := Submodule.finrank_mono (sup_le hWZ hTZ)
  rw [hW, hT] at hdim
  dsimp only [Z] at hsup
  omega

end PreAbstractSimplicialComplex.ModTwoCochains
