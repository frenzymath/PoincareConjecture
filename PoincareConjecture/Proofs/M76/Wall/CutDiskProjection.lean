import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

open Set Geometry

namespace Geometry

theorem PolyhedralPLInCharts.project
    {V E X Y ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X E}
    {d : κ → OpenPartialHomeomorph Y E} (index : κ → ι)
    {p : Y → X} (hp : Continuous p)
    (hsource : ∀ k, MapsTo p (d k).source (e (index k)).source)
    (hval : ∀ k, EqOn (d k) ((e (index k)) ∘ p) (d k).source)
    {j : V → Y} {S : Set V} (hj : PolyhedralPLInCharts d j S) :
    PolyhedralPLInCharts e (p ∘ j) S := by
  refine ⟨hp.comp_continuousOn hj.continuousOn, ?_⟩
  intro x
  obtain ⟨k, J, W, hJ, hJS, hW, hxW, hWJ, hjJ, hcoords⟩ := hj.coordinates x
  refine ⟨index k, J, W, hJ, hJS, hW, hxW, hWJ,
    fun y hy => hsource k (hjJ hy), ?_⟩
  apply hcoords.congr
  intro y hy
  exact hval k (hjJ hy)

end Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_projected_proper_cut_map
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] {Y F : Set X}
    {e : ι → OpenPartialHomeomorph X V3}
    {d : ι × Y → OpenPartialHomeomorph Y V3}
    (hFY : F ⊆ Y)
    (hsource : ∀ k, MapsTo (Subtype.val : Y → X) (d k).source (e k.1).source)
    (hval : ∀ k, (d k : Y → V3) = (e k.1) ∘ Subtype.val)
    {P : Set Y} (hfront : frontier P = (Subtype.val : Y → X) ⁻¹' F)
    {S T : Set V} {j : V → Y} (hj : PolyhedralPLInCharts d j S)
    (hemb : Topology.IsEmbedding (fun x : S => j x.val))
    (gamma : C(T, ↥((Subtype.val : Y → X) ⁻¹' F)))
    (hrim : ∀ x : T, j x.val = (gamma x : Y))
    (hproper : ∀ x : S, j x.val ∈ frontier P ↔ x.val ∈ T) :
    ∃ H : ((Subtype.val : Y → X) ⁻¹' F) ≃ₜ F,
      (∀ x, (H x : X) = ((x : Y) : X)) ∧
      PolyhedralPLInCharts e ((Subtype.val : Y → X) ∘ j) S ∧
      Topology.IsEmbedding (fun x : S => (j x.val : X)) ∧
      MapsTo ((Subtype.val : Y → X) ∘ j) S Y ∧
      (∀ x : T, (j x.val : X) = (H (gamma x) : X)) ∧
      ∀ x : S, (j x.val : X) ∈ F ↔ x.val ∈ T := by
  have hrange : F ⊆ range (Subtype.val : Y → X) := by
    simpa only [Subtype.range_coe] using hFY
  let H := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hrange
  refine ⟨H, fun _ => rfl,
    hj.project Prod.fst continuous_subtype_val hsource
      (fun k y _ => congrFun (hval k) y),
    Topology.IsEmbedding.subtypeVal.comp hemb,
    fun x _ => (j x).property, ?_, ?_⟩
  · intro x
    change (j x.val : X) = ((gamma x : Y) : X)
    exact congrArg (Subtype.val : Y → X) (hrim x)
  · intro x
    change j x.val ∈ (Subtype.val : Y → X) ⁻¹' F ↔ x.val ∈ T
    rw [← hfront]
    exact hproper x

end PoincareConjecture.M76
