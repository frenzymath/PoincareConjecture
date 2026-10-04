import PoincareLib.Topology.Manifold.Surgery.Event.Sum.SumAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Assembly.AssemblyTransport
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentDecomposition
import PoincareLib.Topology.Manifold.Surgery.Event.Union.UnionComparison

/-!
# Combining the classified assemblies of actual components

Concatenate the supplied finite component assemblies by retaining each
other component through every operation. The final union comparison uses
the actual component-region maps to recover the original carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- Combine two supplied assemblies on their actual disjoint-sum target.
Both initial families and every operation are retained through sum lifting
and target swaps. This is the finite packaging step in Proposition 15.3. -/
theorem exists_sumAssemblyPair {m n : ℕ}
    {p : Fin m → GeneralizedSliceCarrier.{u}}
    {q : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly p A)
    (T : SmoothFiniteConnectedSumAssembly q B)
    (hA : Nonempty A.carrier) (hB : Nonempty B.carrier) :
    Nonempty (SmoothFiniteConnectedSumAssembly (Fin.append p q) (sumCarrier A B)) := by
  let R : SmoothFiniteConnectedSumAssembly (Fin.append p q) (sumCarrier A T.initial) := {
    initial := sumCarrier S.initial T.initial
    disjoint_union := sumRefinement S.disjoint_union T.disjoint_union
      (connectedSumChain_source_nonempty S.operations hA)
      (connectedSumChain_source_nonempty T.operations hB)
    operations := sumConnectedSumChain S.operations T.initial }
  obtain ⟨R'⟩ := exists_transportAssembly (B := sumCarrier T.initial A) R
    (Diffeomorph.sumComm (𝓡 3) A.carrier ∞ T.initial.carrier)
  exact exists_transportAssembly (R'.trans (sumConnectedSumChain T.operations A))
    (Diffeomorph.sumComm (𝓡 3) B.carrier ∞ A.carrier)

/-- For a nonempty finite family of actual nonempty components, concatenate
the supplied classified assemblies and keep a union of the original
components on the same model target. This intermediate target is only a
finite disjoint sum of the supplied carriers. -/
private theorem exists_classifiedAssemblyModel (m : ℕ)
    (B : Fin (m + 1) → GeneralizedSliceCarrier.{u})
    (hB : ∀ i, Nonempty (B i).carrier)
    (hcomponent : ∀ i, ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (Set.univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (Set.univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
        Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D (B i))) :
    ∃ C : GeneralizedSliceCarrier.{u}, ∃ U : SmoothDisjointUnionData B C,
      Nonempty C.carrier ∧
      ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
        (∀ j, IsCompact (Set.univ : Set (D j).carrier)) ∧
        (∀ j, IsConnected (Set.univ : Set (D j).carrier)) ∧
        (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
          Nonempty (SurgeryPositiveSpaceform (D j))) ∧
        Nonempty (SmoothFiniteConnectedSumAssembly D C) := by
  classical
  induction m with
  | zero =>
      obtain ⟨n, D, hc, hn, hs, hS⟩ := hcomponent 0
      have hfamily : (fun _ : Fin 1 => B 0) = B :=
        funext (fun i => congrArg B (Subsingleton.elim 0 i))
      exact ⟨B 0, hfamily ▸ singletonDisjointUnion (B 0), hB 0, n, D, hc, hn, hs, hS⟩
  | succ m ih =>
      obtain ⟨C, U, hC, n, D, hc, hn, hs, ⟨S⟩⟩ :=
        ih (fun i => B i.castSucc) (fun i => hB i.castSucc)
          (fun i => hcomponent i.castSucc)
      obtain ⟨k, E, hcE, hnE, hsE, ⟨T⟩⟩ := hcomponent (Fin.last (m + 1))
      have hfamily : Fin.append (fun i : Fin (m + 1) => B i.castSucc)
          (fun _ : Fin 1 => B (Fin.last (m + 1))) = B := by
        funext i
        refine Fin.addCases ?_ ?_ i
        · intro j
          rw [Fin.append_left]
          rfl
        · intro j
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          rw [Fin.append_right]
          rfl
      let appendedUnion : SmoothDisjointUnionData
          (Fin.append (fun i : Fin (m + 1) => B i.castSucc)
            (fun _ : Fin 1 => B (Fin.last (m + 1))))
          (sumCarrier C (B (Fin.last (m + 1)))) :=
        sumRefinement U (singletonDisjointUnion (B (Fin.last (m + 1))))
          hC (hB (Fin.last (m + 1)))
      refine ⟨sumCarrier C (B (Fin.last (m + 1))),
        Eq.mp (congrArg (fun family => SmoothDisjointUnionData family
          (sumCarrier C (B (Fin.last (m + 1))))) hfamily) appendedUnion,
        ⟨Sum.inl (Classical.choice hC)⟩, n + k, Fin.append D E, ?_, ?_, ?_,
        exists_sumAssemblyPair S T hC (hB (Fin.last (m + 1)))⟩
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          rw [Fin.append_left]
          exact hc j
        · intro j
          rw [Fin.append_right]
          exact hcE j
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          rw [Fin.append_left]
          exact hn j
        · intro j
          rw [Fin.append_right]
          exact hnE j
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          rw [Fin.append_left]
          exact hs j
        · intro j
          rw [Fin.append_right]
          exact hsE j

/-- Morgan--Tian Proposition 15.3, pp. 357-358: classified finite assemblies
of every actual component combine into one classified finite assembly of
the actual compact carrier. Empty carriers use their empty component union.
This theorem assumes each component's assembly, not a topology classification
or a sphere-filling principle for arbitrary regions. -/
theorem exists_classifiedAssembly_of_components (A : GeneralizedSliceCarrier.{u})
    (hA : IsCompact (Set.univ : Set A.carrier))
    (hcomponent : ∀ x : A.carrier,
      ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
        (∀ j, IsCompact (Set.univ : Set (D j).carrier)) ∧
        (∀ j, IsConnected (Set.univ : Set (D j).carrier)) ∧
        (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
          Nonempty (SurgeryPositiveSpaceform (D j))) ∧
        Nonempty (SmoothFiniteConnectedSumAssembly D (componentCarrier A x))) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (Set.univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (Set.univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
        Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D A) := by
  obtain ⟨m, r, U, _⟩ := exists_component_decomposition A hA
  cases m with
  | zero =>
      exact ⟨0, (fun i => componentCarrier A (r i)),
        (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
        ⟨U.toAssembly⟩⟩
  | succ m =>
      have hnonempty (i : Fin (m + 1)) : Nonempty (componentCarrier A (r i)).carrier :=
        ⟨⟨r i, mem_connectedComponent⟩⟩
      obtain ⟨C, V, _, n, D, hc, hn, hs, ⟨S⟩⟩ :=
        exists_classifiedAssemblyModel m (fun i => componentCarrier A (r i))
          hnonempty (fun i => hcomponent (r i))
      exact ⟨n, D, hc, hn, hs,
        exists_transportAssembly S (unionComparisonDiffeomorph V U)⟩

end PoincareMT.M38
