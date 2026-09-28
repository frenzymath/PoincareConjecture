import PoincareConjecture.Proofs.M59.Mathlib.PathClassSheets
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

open Set TopologicalSpace Function Bundle
open scoped Topology

universe u

class LocallySimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop where

  exists_open_simplyConnected : ∀ (x : X) (U : Set X), x ∈ U → IsOpen U →
    ∃ V : Set X, IsOpen V ∧ IsSimplyConnected V ∧ x ∈ V ∧ V ⊆ U

namespace PathClassCover

variable {X : Type u} [TopologicalSpace X]

def sheetBasis (x₀ : X) : Set (Set (PathClassCover x₀)) :=
  {S | ∃ (U : Set X) (a : PathClassCover x₀),
    IsOpen U ∧ IsSimplyConnected U ∧ a.endpoint ∈ U ∧ S = sheet U a}

instance (x₀ : X) : TopologicalSpace (PathClassCover x₀) :=
  TopologicalSpace.generateFrom (sheetBasis x₀)

theorem isOpen_sheet {x₀ : X} {U : Set X} (hU : IsOpen U)
    (hsc : IsSimplyConnected U) (a : PathClassCover x₀) (ha : a.endpoint ∈ U) :
    IsOpen (sheet U a) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨U, a, hU, hsc, ha, rfl⟩

variable [LocallySimplyConnectedSpace X]

theorem isTopologicalBasis (x₀ : X) : IsTopologicalBasis (sheetBasis x₀) where
  exists_subset_inter := by
    rintro _ ⟨U, a, hU, hscU, ha, rfl⟩ _ ⟨V, b, hV, hscV, hb, rfl⟩ c hc
    obtain ⟨W, hW, hscW, hcW, hWUV⟩ :=
      LocallySimplyConnectedSpace.exists_open_simplyConnected c.endpoint (U ∩ V)
        ⟨endpoint_mem_of_mem_sheet hc.1, endpoint_mem_of_mem_sheet hc.2⟩ (hU.inter hV)
    refine ⟨sheet W c, ⟨W, c, hW, hscW, hcW, rfl⟩, mem_sheet_self c hcW, ?_⟩
    intro d hd
    constructor
    · rw [← sheet_eq_of_mem hc.1]
      exact sheet_mono (hWUV.trans inter_subset_left) c hd
    · rw [← sheet_eq_of_mem hc.2]
      exact sheet_mono (hWUV.trans inter_subset_right) c hd
  sUnion_eq := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨U, hU, hsc, ha, _⟩ :=
      LocallySimplyConnectedSpace.exists_open_simplyConnected a.endpoint univ
        (mem_univ _) isOpen_univ
    exact Set.mem_sUnion.mpr ⟨sheet U a, ⟨U, a, hU, hsc, ha, rfl⟩, mem_sheet_self a ha⟩
  eq_generateFrom := rfl

theorem continuous_endpoint (x₀ : X) : Continuous (endpoint : PathClassCover x₀ → X) := by
  apply continuous_def.mpr
  intro U hU
  apply (isTopologicalBasis x₀).isOpen_iff.mpr
  intro a ha
  obtain ⟨V, hV, hsc, hav, hVU⟩ :=
    LocallySimplyConnectedSpace.exists_open_simplyConnected a.endpoint U ha hU
  exact ⟨sheet V a, ⟨V, a, hV, hsc, hav, rfl⟩, mem_sheet_self a hav,
    fun _ hb => hVU (endpoint_mem_of_mem_sheet hb)⟩

theorem isOpenMap_endpoint (x₀ : X) : IsOpenMap (endpoint : PathClassCover x₀ → X) := by
  apply (isTopologicalBasis x₀).isOpenMap_iff.mpr
  rintro _ ⟨U, a, hU, hsc, ha, rfl⟩
  simpa only [image_sheet hsc.isPathConnected a ha] using hU

omit [LocallySimplyConnectedSpace X] in

theorem pairwise_disjoint_sheets {x₀ x : X} {U : Set X} (hsc : IsSimplyConnected U)
    (hx : x ∈ U) : Pairwise (Disjoint on
      (fun a : Path.Homotopic.Quotient x₀ x => sheet U ⟨x, a⟩)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro c hca hcb
  have he : sheet U (⟨x, a⟩ : PathClassCover x₀) = sheet U ⟨x, b⟩ :=
    (sheet_eq_of_mem hca).symm.trans (sheet_eq_of_mem hcb)
  have ha : (⟨x, a⟩ : PathClassCover x₀) ∈ sheet U ⟨x, b⟩ :=
    he ▸ mem_sheet_self ⟨x, a⟩ hx
  have h := endpoint_injOn_sheet hsc (⟨x, b⟩ : PathClassCover x₀)
    ha (mem_sheet_self _ hx) rfl
  exact hab (eq_of_heq (PathClassCover.mk.inj h).2)

omit [LocallySimplyConnectedSpace X] in

theorem sheets_exhaustive {x₀ x : X} {U : Set X} (hsc : IsSimplyConnected U)
    (hx : x ∈ U) :
    endpoint ⁻¹' U ⊆ ⋃ a : Path.Homotopic.Quotient x₀ x, sheet U ⟨x, a⟩ := by
  intro b hb
  obtain ⟨p, hp⟩ := hsc.isPathConnected.joinedIn b.endpoint hb x hx
  let a : Path.Homotopic.Quotient x₀ x := b.pathClass.trans (.mk p)
  have ha : (⟨x, a⟩ : PathClassCover x₀) ∈ sheet U b := ⟨p, hp, rfl⟩
  exact mem_iUnion.mpr ⟨a, mem_sheet_symm ha⟩

theorem isCoveringMap_endpoint [PathConnectedSpace X] (x₀ : X) :
    IsCoveringMap (endpoint : PathClassCover x₀ → X) := by
  classical
  intro x
  obtain ⟨U, hU, hsc, hx, _⟩ :=
    LocallySimplyConnectedSpace.exists_open_simplyConnected x univ (mem_univ _) isOpen_univ
  let I := Path.Homotopic.Quotient x₀ x
  let : TopologicalSpace I := ⊥
  let : DiscreteTopology I := ⟨rfl⟩
  let : Nonempty I := ⟨.mk (PathConnectedSpace.somePath x₀ x)⟩
  let : Nonempty (X → PathClassCover x₀) := ⟨fun _ => basepoint x₀⟩
  let T : Trivialization I (endpoint : PathClassCover x₀ → X) :=
    hU.trivializationDiscrete (fun a : I => sheet U ⟨x, a⟩) U
      (fun a W hWU => by
        constructor
        · intro hW
          exact (hW.preimage (continuous_endpoint x₀)).inter (isOpen_sheet hU hsc _ hx)
        · intro hW
          have he : endpoint '' (endpoint ⁻¹' W ∩ sheet U (⟨x, a⟩ : PathClassCover x₀)) = W := by
            apply Set.Subset.antisymm
            · rintro _ ⟨b, hb, rfl⟩
              exact hb.1
            · intro y hy
              obtain ⟨b, hb, hby⟩ := endpoint_surjOn_sheet hsc.isPathConnected
                (⟨x, a⟩ : PathClassCover x₀) hx (hWU hy)
              exact ⟨b, ⟨by change b.endpoint ∈ W; rwa [hby], hb⟩, hby⟩
          exact he ▸ isOpenMap_endpoint x₀ _ hW)
      (fun a => endpoint_injOn_sheet hsc ⟨x, a⟩)
      (fun a => endpoint_surjOn_sheet hsc.isPathConnected ⟨x, a⟩ hx)
      (pairwise_disjoint_sheets hsc hx) (sheets_exhaustive hsc hx)
  exact (IsEvenlyCovered.of_trivialization (t := T) hx).to_isEvenlyCovered_preimage

end PathClassCover
