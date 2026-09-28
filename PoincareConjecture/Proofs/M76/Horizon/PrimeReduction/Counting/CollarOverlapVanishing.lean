import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CollarOverlapHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarOverlapCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalSphereSimplyConnected
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Product









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set CategoryTheory Limits HomologicalComplex
open Poincare.Topology

universe u v w

namespace PoincareConjecture.M76.CollarOverlap

theorem endInterval_contractible (b : Bool) : ContractibleSpace (endInterval b) := by
  apply (convex_Ioo _ _).contractibleSpace
  apply nonempty_Ioo.mpr
  cases b <;> norm_num

theorem overlap_h1_isZero_same_universe
    {X κ : Type u} [TopologicalSpace X] [T2Space X] [Finite κ]
    {A : κ → Type u} [∀ i, TopologicalSpace (A i)]
    [∀ i, CompactSpace (A i)] [∀ i, SimplyConnectedSpace (A i)]
    {C : κ → Set X}
    (R : Set X) (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hCR : ∀ i, C i ⊆ R) (hOC : ∀ i, O i ⊆ C i)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    IsZero (ModTwoMayerVietoris.homology
      ↥(collarCoverOuter R W ∩ collarCoverInner R O) 1) := by
  let : ∀ b, ContractibleSpace (endInterval b) := endInterval_contractible
  let : ∀ k : κ × Bool, SimplyConnectedSpace (A k.1 × endInterval k.2) :=
    fun _ => simplyConnectedSpace_prod_contractible
  obtain ⟨H, _⟩ := exists_overlap_homeomorph R O W hCR hOC hdis hO
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Σ k : κ × Bool, A k.1 × endInterval k.2))
      (Y := TopCat.of ↥(collarCoverOuter R W ∩ collarCoverInner R O)) H)
  let e := ((homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) 1).mapIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
      ModTwoMayerVietoris.coefficient).mapIso iso))
  exact (sigma_h1_isZero (fun k : κ × Bool => A k.1 × endInterval k.2)).of_iso e.symm

theorem overlap_h1_isZero
    {X : Type u} {κ : Type v} [TopologicalSpace X] [T2Space X] [Finite κ]
    {A : κ → Type u} [∀ i, TopologicalSpace (A i)]
    [∀ i, CompactSpace (A i)] [∀ i, SimplyConnectedSpace (A i)]
    {C : κ → Set X}
    (R : Set X) (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hCR : ∀ i, C i ⊆ R) (hOC : ∀ i, O i ⊆ C i)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    IsZero (ModTwoMayerVietoris.homology
      ↥(collarCoverOuter R W ∩ collarCoverInner R O) 1) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let J := ULift.{u} (Fin (Fintype.card κ))
  let E : J ≃ κ := Equiv.ulift.trans (Fintype.equivFin κ).symm
  have hh := overlap_h1_isZero_same_universe R (fun j : J => O (E j))
    (fun j : J => W (E j)) (fun j => hCR (E j)) (fun j => hOC (E j))
    (fun _ _ h => hdis (fun he => h (E.injective he))) (fun j => hO (E j))
  have houter : collarCoverOuter R (fun j : J => W (E j)) = collarCoverOuter R W := by
    exact congrArg (fun T : Set X => (Subtype.val : R → X) ⁻¹' Tᶜ)
      (E.surjective.iUnion_comp (fun i => collarMiddle (W i)))
  have hinner : collarCoverInner R (fun j : J => O (E j)) = collarCoverInner R O := by
    unfold collarCoverInner
    rw [E.surjective.iUnion_comp]
  rw [houter, hinner] at hh
  exact hh


theorem marked_sphere_overlap_h1_isZero
    {X : Type u} {κ : Type v} {ι : Type w} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S : κ → Set X}
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (R Q : Set X) (O : κ → Set X) (B : κ × Bool → Set X)
    (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (H : ∀ i b, S i ≃ₜ B (i, b))
    (hQ : Q = R \ ⋃ i, O i)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hinc : ∀ i, closure (O i) ∩ Q = B (i, false) ∪ B (i, true))
    (hW : ∀ i a, (W i (a, 0) : X) = H i false a ∧
      (W i (a, 1) : X) = H i true a) :
    IsZero (ModTwoMayerVietoris.homology
      ↥(collarCoverOuter R W ∩ collarCoverInner R O) 1) := by
  let : CompactSpace (Metric.sphere (0 : Fin 3 → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : ∀ i, CompactSpace (S i) := fun i => (sS i).parametrization.compactSpace
  let : ∀ i, SimplyConnectedSpace (S i) := fun i => (sS i).simplyConnectedSpace
  exact overlap_h1_isZero R O W hCR (fun _ => subset_closure) hdis
    (marked_cut_collar_open_iff R Q O B W H hQ hCR hdis hinc hW)

end PoincareConjecture.M76.CollarOverlap
