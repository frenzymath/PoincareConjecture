import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

open Metric Set Topology

universe u v

namespace Poincare.Topology

theorem exists_finiteCW_of_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (univ : Set X)] [CWComplex.Finite (univ : Set X)]
    (h : X ≃ₜ Y) :
    ∃ D : CWComplex (univ : Set Y),
      letI := D
      CWComplex.Finite (univ : Set Y) ∧
        ∀ n : ℕ, Nonempty (Topology.CWComplex.cell (univ : Set Y) n ≃
          Topology.CWComplex.cell (univ : Set X) n) := by
  classical
  let oldCell : ℕ → Type u := fun n => Topology.RelCWComplex.cell (univ : Set X) n
  let oldFinite (n : ℕ) : _root_.Finite (oldCell n) :=
    Topology.CWComplex.FiniteType.finite_cell (C := (univ : Set X)) n
  let oldFintype (n : ℕ) : Fintype (oldCell n) := Fintype.ofFinite _
  let newCell : ℕ → Type v :=
    fun n => ULift.{v} (Fin (Fintype.card (oldCell n)))
  let cellEquiv (n : ℕ) : newCell n ≃ oldCell n :=
    Equiv.ulift.trans (Fintype.equivFin (oldCell n)).symm
  let indexEquiv : (Σ n, newCell n) ≃ (Σ n, oldCell n) :=
    Equiv.sigmaCongrRight cellEquiv
  let newMap : (n : ℕ) → newCell n → PartialEquiv (Fin n → ℝ) Y :=
    fun n i => (Topology.RelCWComplex.map (C := (univ : Set X)) n (cellEquiv n i)).transEquiv
      h.toEquiv
  have hsource (n : ℕ) (i : newCell n) : (newMap n i).source = ball 0 1 := by
    exact Topology.RelCWComplex.source_eq (C := (univ : Set X)) n (cellEquiv n i)
  have hcontinuous (n : ℕ) (i : newCell n) :
      ContinuousOn (newMap n i) (closedBall 0 1) := by
    exact h.continuous.comp_continuousOn
      (Topology.RelCWComplex.continuousOn (C := (univ : Set X)) n (cellEquiv n i))
  have hinverse (n : ℕ) (i : newCell n) :
      ContinuousOn (newMap n i).symm (newMap n i).target := by
    exact (Topology.RelCWComplex.continuousOn_symm (C := (univ : Set X)) n (cellEquiv n i)).comp
      h.symm.continuous.continuousOn (fun _ hx => hx)
  have hfinite (n : ℕ) : _root_.Finite (newCell n) := inferInstance
  have heventually : ∀ᶠ n in Filter.atTop, IsEmpty (newCell n) := by
    have hold : ∀ᶠ n in Filter.atTop, IsEmpty (oldCell n) := by
      change ∀ᶠ n in Filter.atTop,
        IsEmpty (Topology.RelCWComplex.cell (univ : Set X) n)
      exact Topology.CWComplex.FiniteDimensional.eventually_isEmpty_cell
    filter_upwards [hold] with n hn
    let : IsEmpty (oldCell n) := hn
    exact ⟨fun i => isEmptyElim (cellEquiv n i)⟩
  have hdisjoint :
      (univ : Set (Σ n, newCell n)).PairwiseDisjoint
        (fun ni => newMap ni.1 ni.2 '' ball 0 1) := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    change Disjoint
      ((h ∘ Topology.RelCWComplex.map (C := (univ : Set X)) n (cellEquiv n i)) '' ball 0 1)
      ((h ∘ Topology.RelCWComplex.map (C := (univ : Set X)) m (cellEquiv m j)) '' ball 0 1)
    rw [image_comp, image_comp, disjoint_image_iff h.injective]
    change Disjoint
      (Topology.RelCWComplex.openCell n (cellEquiv n i))
      (Topology.RelCWComplex.openCell m (cellEquiv m j))
    apply Topology.CWComplex.disjoint_openCell_of_ne
    intro hold
    apply hne
    exact indexEquiv.injective hold
  have hattach (n : ℕ) (i : newCell n) :
      MapsTo (newMap n i) (sphere 0 1)
        (⋃ (m < n) (j : newCell m), newMap m j '' closedBall 0 1) := by
    obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo (C := (univ : Set X)) n (cellEquiv n i)
    intro x hx
    change h (Topology.RelCWComplex.map (C := (univ : Set X)) n (cellEquiv n i) x) ∈ _
    obtain ⟨m, hm, j, _, z, hz, hzx⟩ := by
      simpa only [mem_iUnion, mem_image] using hI hx
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm, mem_iUnion.mpr
      ⟨(cellEquiv m).symm j, z, hz, ?_⟩⟩⟩
    simpa only [newMap, PartialEquiv.coe_transEquiv, Homeomorph.coe_toEquiv,
      Function.comp_apply, Equiv.apply_symm_apply] using congrArg h hzx
  have hcover :
      ⋃ (n : ℕ) (i : newCell n), newMap n i '' closedBall 0 1 =
        (univ : Set Y) := by
    apply Subset.antisymm (subset_univ _)
    intro y _
    have hx : h.symm y ∈
        ⋃ (n : ℕ) (i : oldCell n),
          Topology.RelCWComplex.map (C := (univ : Set X)) n i '' closedBall 0 1 := by
      change h.symm y ∈ ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell (univ : Set X) n),
        Topology.CWComplex.closedCell n i
      rw [Topology.CWComplex.union]
      exact mem_univ _
    obtain ⟨n, i, z, hz, hzy⟩ := by
      simpa only [mem_iUnion, mem_image] using hx
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨(cellEquiv n).symm i, z, hz, ?_⟩⟩
    simpa only [newMap, PartialEquiv.coe_transEquiv, Homeomorph.coe_toEquiv,
      Function.comp_apply, Equiv.apply_symm_apply] using
      (congrArg h hzy).trans (h.apply_symm_apply y)
  let D := CWComplex.mkFinite (univ : Set Y) newCell newMap heventually hfinite
    hsource hcontinuous hinverse hdisjoint hattach hcover
  refine ⟨D, ?_⟩
  let := D
  refine ⟨CWComplex.finite_mkFinite (univ : Set Y) newCell newMap heventually hfinite
      hsource hcontinuous hinverse hdisjoint hattach hcover, ?_⟩
  intro n
  exact ⟨cellEquiv n⟩

end Poincare.Topology
