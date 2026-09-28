import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Commensurable
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.RetainedPair
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.AtlasRange

set_option autoImplicit false
open Set Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76
open PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem exists_original_marked_product_of_retained_component
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R S₀ S₁ : Set X0}
    (hI : IsPLIrreducible e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁) (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X0) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X0) = S₁)
    (hnt₀ : Nontrivial (FundamentalGroup S₀ x₀))
    (hnt₁ : Nontrivial (FundamentalGroup S₁ x₁))
    (hinj₀ : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S₀, X0)) x₀))
    (hinj₁ : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S₁, X0)) x₁))
    (k : Path
      ((ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁)).range)) :
    ∃ H : (S₀ × unitInterval) ≃ₜ R,
      (∀ x, (H (x, ⟨0, by norm_num⟩) : X0) = x) ∧
      range (fun x => (H (x, ⟨1, by norm_num⟩) : X0)) = S₁ ∧
      (∀ x t, (H (x, t) : X0) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X0 → (s → ℝ × V3))
        (HG : ((G '' S₀) ×ˢ Set.Icc (0 : ℝ) 1) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X0, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : S₀) (t : unitInterval),
          (HG ⟨(G x, t), ⟨mem_image_of_mem G x.property, t.property⟩⟩ :
            s → ℝ × V3) = G (H (x, t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X0) (b : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  classical
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let S (b : Bool) := if b then S₁ else S₀
  let x : ∀ b, S b := fun b => by cases b <;> assumption
  obtain ⟨T, v, hv, hvalue, _⟩ := hI.1.exists_original_retained_PL_torus_pair hR S
    (fun b => by cases b <;> assumption) x
    (fun b => by cases b <;> assumption)
    (fun b => by cases b <;> assumption)
    (fun b => by cases b <;> assumption)
  have hinjR₀ : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀) := by
    have h := hinj₀
    change Function.Injective (FundamentalGroup.map
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)).comp
        (ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset))) x₀) at h
    rw [FundamentalGroup.map_comp] at h
    exact Function.Injective.of_comp h
  have hinjR₁ : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁) := by
    have h := hinj₁
    change Function.Injective (FundamentalGroup.map
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)).comp
        (ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset))) x₁) at h
    rw [FundamentalGroup.map_comp] at h
    exact Function.Injective.of_comp h
  obtain ⟨O⟩ := hamiltonZeroAmbient_localOrientation
  obtain ⟨H, hzero, hone, hfront, s, G, HG, hG, hGPL, hGinj,
      hHG, hHGi, hHGvalue, hlocal⟩ :=
    exists_marked_product_of_commensurable_boundary_tori_of_localOrientation
      hI.range hR hconn O hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁
      hinjR₀ hinjR₁ k hcomm (T false) (T true) (v false) (v true)
      (hv false).range (hv true).range (hvalue false) (hvalue true)
  refine ⟨H, hzero, hone, hfront, s, G, HG, hG,
    (fun i => hGPL ⟨e i, mem_range_self i⟩), hGinj, hHG, hHGi, hHGvalue, ?_⟩
  intro z hz
  obtain ⟨i, V, b, hV, hzV, hVi, hvalue⟩ := hlocal z hz
  obtain ⟨j, hj⟩ := i.property
  refine ⟨j, V, b, hV, hzV, ?_, ?_⟩
  · simpa only [hj] using hVi
  · simpa only [hj] using hvalue

end PoincareConjecture.M76
