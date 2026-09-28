import PoincareConjecture.Proofs.M76.Brown.LocallyFlatOrientedBicollar
import PoincareConjecture.Proofs.M76.Brown.BicollarEndGeometry
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option autoImplicit false

open Set Metric Topology
open scoped OnePoint

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "X3" => OnePoint V3
local notation "T2" => sphere (0 : V3) 1

theorem exists_compactified_bicollar {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ D : Set V3, IsCompact D ∧ frontier D = S ∧ S ⊆ D ∧
      ∃ U V : Set X3, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
        U ∪ V = (((↑) : V3 → X3) '' S)ᶜ ∧
        U ⊆ ((↑) : V3 → X3) '' D ∧ V = (((↑) : V3 → X3) '' D)ᶜ ∧
        ∃ e : OpenPartialHomeomorph (T2 × Ioo (-1 : ℝ) 1) X3,
          e.source = univ ∧ BrownSchoenflies.bicollarBaseImage e = ((↑) : V3 → X3) '' S ∧
          (∀ z, (z.2 : ℝ) < 0 → e z ∈ U) ∧
          (∀ z, 0 < (z.2 : ℝ) → e z ∈ V) ∧
          (∀ z, e z ∈ ((↑) : V3 → X3) '' D ↔ (z.2 : ℝ) ≤ 0) := by
  classical
  obtain ⟨U, V, O, hU, hV, hdis, hunion, hfrontU, _, hcompact,
    hfront, hO, _, H, hbase, hneg, hpos⟩ := hS.exists_bounded_oriented_bicollar
  have hD : closure U = Vᶜ := BrownCollar.closure_region_eq_compl hdis hunion hfrontU
  have hSD : S ⊆ closure U := by
    rw [← hfrontU]
    exact frontier_subset_closure
  let J : (T2 × Ioo (-1 : ℝ) 1) ≃ₜ O :=
    (hS.parametrization.prodCongr (Homeomorph.refl _)).trans H
  let f : (T2 × Ioo (-1 : ℝ) 1) → X3 :=
    fun z => ((J z : V3) : X3)
  have hf : IsOpenEmbedding f := OnePoint.isOpenEmbedding_coe.comp
    (hO.isOpenEmbedding_subtypeVal.comp J.isOpenEmbedding)
  have hT : (sphere (0 : V3) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty T2 := hT.to_subtype
  let : Nonempty (Ioo (-1 : ℝ) 1) := ⟨⟨0, by constructor <;> norm_num⟩⟩
  let e := hf.toOpenPartialHomeomorph f
  have hes : e.source = univ := rfl
  have he (z : T2 × Ioo (-1 : ℝ) 1) :
      e z = ((H (hS.parametrization z.1, z.2) : V3) : X3) := rfl
  have hebase (u : T2) :
      e (BrownCollar.bicollarBase u) = ((hS.parametrization u : V3) : X3) := by
    rw [he]
    exact congrArg ((↑) : V3 → X3) (hbase (hS.parametrization u))
  have hbaseImage : BrownSchoenflies.bicollarBaseImage e = ((↑) : V3 → X3) '' S := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨hS.parametrization u, (hS.parametrization u).property, (hebase u).symm⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨u, hu⟩ := hS.parametrization.surjective ⟨s, hs⟩
      exact ⟨u, (hebase u).trans (congrArg (fun z : S => ((z : V3) : X3)) hu)⟩
  have hheight (z : T2 × Ioo (-1 : ℝ) 1) :
      e z ∈ ((↑) : V3 → X3) '' closure U ↔ (z.2 : ℝ) ≤ 0 := by
    rw [he, OnePoint.coe_injective.mem_set_image, hD]
    change (H (hS.parametrization z.1, z.2) : V3) ∉ V ↔ _
    constructor
    · intro hz
      exact le_of_not_gt (fun h => hz (hpos _ h))
    · intro hz
      rcases lt_or_eq_of_le hz with hlt | heq
      · exact fun hx => Set.disjoint_left.mp hdis (hneg _ hlt) hx
      · have hzbase : (hS.parametrization z.1, z.2) =
            BrownCollar.bicollarBase (hS.parametrization z.1) :=
          Prod.ext rfl (Subtype.ext heq)
        rw [hzbase, hbase]
        exact fun hx => (hunion.subset (Or.inr hx)) (hS.parametrization z.1).property
  let U' : Set X3 := ((↑) : V3 → X3) '' U
  let V' : Set X3 := (((↑) : V3 → X3) '' closure U)ᶜ
  have hU'D : U' ⊆ ((↑) : V3 → X3) '' closure U := image_mono subset_closure
  have hdis' : Disjoint U' V' := Set.disjoint_left.mpr fun _ hu hv => hv (hU'D hu)
  have hunion' : U' ∪ V' = (((↑) : V3 → X3) '' S)ᶜ := by
    ext x
    induction x using OnePoint.rec with
    | infty => simp [U', V']
    | coe x =>
        change ((x : X3) ∈ ((↑) : V3 → X3) '' U ∨
          (x : X3) ∉ ((↑) : V3 → X3) '' closure U) ↔
          (x : X3) ∉ ((↑) : V3 → X3) '' S
        simp only [OnePoint.coe_injective.mem_set_image, hD, mem_compl_iff, not_not]
        exact Set.ext_iff.mp hunion x
  refine ⟨closure U, hcompact, hfront, hSD, U', V',
    OnePoint.isOpen_image_coe.mpr hU,
    OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closure, hcompact⟩,
    hdis', hunion', hU'D, rfl, e, hes, hbaseImage, ?_, ?_, hheight⟩
  · intro z hz
    exact ⟨H (hS.parametrization z.1, z.2), hneg _ hz, (he z).symm⟩
  · intro z hz
    exact fun hx => not_le_of_gt hz ((hheight z).mp hx)

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
