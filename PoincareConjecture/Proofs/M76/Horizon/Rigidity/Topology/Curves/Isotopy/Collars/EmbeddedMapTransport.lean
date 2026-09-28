import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift

set_option autoImplicit false
open Set Geometry Metric Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLHomeomorph.exists_polyhedralPL_parameter_transport
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] {R : Set X}
    {e : ι → OpenPartialHomeomorph X V3} {G : R ≃ₜ R}
    (hG : ChartwisePLHomeomorph e e G)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (j : E → X) (hj : PolyhedralPLInCharts e j K.space)
    (original : C(K.space, R)) (hvalue : ∀ x : K.space, j x = (original x : X)) :
    ∃ g : E → X, PolyhedralPLInCharts e g K.space ∧
      ∀ x : K.space, g x = (G (original x) : X) := by
  classical
  by_cases hne : K.space.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let q : E → R := fun x => if hx : x ∈ K.space then original ⟨x, hx⟩ else original ⟨x₀, hx₀⟩
    have hq (x : K.space) : q x = original x := by simp only [q, dif_pos x.property]
    have hqc : ContinuousOn q K.space := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun x : K.space => q x)
      have heq : (fun x : K.space => q x) = original := funext hq
      rw [heq]
      exact original.continuous
    have hqPL : PolyhedralPLInCharts e (fun x => (q x : X)) K.space := hj.congr (by
      intro x hx
      exact (hvalue ⟨x, hx⟩).trans (congrArg Subtype.val (hq ⟨x, hx⟩)).symm)
    refine ⟨fun x => (G (q x) : X),
      hG.1.polyhedralPLInCharts_comp K hK q hqc hqPL (fun _ _ => mem_univ _), ?_⟩
    intro x
    change (G (q x) : X) = G (original x)
    rw [hq]
  · refine ⟨j, hj, ?_⟩
    intro x
    exact (hne ⟨x, x.property⟩).elim

theorem isEmbedding_original_parameter_transport
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {S : Set E} {R : Set X} (G : R ≃ₜ R)
    (j g : E → X) (original : C(S, R))
    (hvalue : ∀ x : S, j x = (original x : X))
    (hnew : ∀ x : S, g x = (G (original x) : X))
    (hemb : IsEmbedding (fun x : S => j x)) :
    IsEmbedding (fun x : S => g x) := by
  have hembOriginal : IsEmbedding original :=
    (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
      (by simpa only [Function.comp_def, ← hvalue] using hemb)
  have hh := Topology.IsEmbedding.subtypeVal.comp (G.isEmbedding.comp hembOriginal)
  simpa only [Function.comp_def, ← hnew] using hh

theorem sourceAnnulusRim_comp_homeomorph
    {X : Type*} [TopologicalSpace X] {R : Set X}
    (G : R ≃ₜ R) (original : C(Dehn.ProtectedAnnulus.source, R)) (b : Bool) :
    sourceAnnulusRim ((⟨G, G.continuous⟩ : C(R, R)).comp original) b =
      (⟨G, G.continuous⟩ : C(R, R)).comp (sourceAnnulusRim original b) := rfl

theorem sourceAnnulusRim_nonnullhomotopic_comp_homeomorph
    {X : Type*} [TopologicalSpace X] {R : Set X}
    (G : R ≃ₜ R) (original : C(Dehn.ProtectedAnnulus.source, R)) (b : Bool)
    (hessential : ¬ (sourceAnnulusRim original b).Nullhomotopic) :
    ¬ (sourceAnnulusRim ((⟨G, G.continuous⟩ : C(R, R)).comp original) b).Nullhomotopic := by
  intro hn
  have hback := hn.comp_right (⟨G.symm, G.symm.continuous⟩ : C(R, R))
  have heq : (⟨G.symm, G.symm.continuous⟩ : C(R, R)).comp
      (sourceAnnulusRim ((⟨G, G.continuous⟩ : C(R, R)).comp original) b) =
        sourceAnnulusRim original b := by
    apply ContinuousMap.ext
    intro z
    exact G.symm_apply_apply _
  exact hessential (heq ▸ hback)

namespace Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_original_embedded_cylinder_transport
    {X ι : Type*} [TopologicalSpace X] {R : Set X}
    {e : ι → OpenPartialHomeomorph X V3}
    (G : R ≃ₜ R) (hG : ChartwisePLHomeomorph e e G)
    (hfront : ∀ x : R, (G x : X) ∈ frontier R ↔ (x : X) ∈ frontier R)
    (j : (V1 × V2) → X) (original : C(source, R))
    (hj : PolyhedralPLInCharts e j source)
    (hemb : IsEmbedding (fun x : source => j x))
    (hvalue : ∀ x : source, j x = (original x : X))
    (hproper : ∀ x : source, j x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hessential : ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic) :
    ∃ (g : (V1 × V2) → X) (moved : C(source, R)),
      PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
      moved = (⟨G, G.continuous⟩ : C(R, R)).comp original ∧
      (∀ x : source, g x = (moved x : X)) ∧
      (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      (∀ b, ¬ (sourceAnnulusRim moved b).Nullhomotopic) ∧
      (∀ x : source, G (original x) = original x → g x = j x) ∧
      (∀ b, (∀ z : Q2, G (sourceAnnulusRim original b z) = sourceAnnulusRim original b z) →
        sourceAnnulusRim moved b = sourceAnnulusRim original b) ∧
      ∀ b (z : Q2), g (endpoint b, z) = (G (sourceAnnulusRim original b z) : X) := by
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  let p : K.space ≃ₜ source := Homeomorph.setCongr hKs
  let originalK : C(K.space, R) := original.comp ⟨p, p.continuous⟩
  have hjK : PolyhedralPLInCharts e j K.space := hKs.symm ▸ hj
  obtain ⟨g, hg, hgv⟩ := hG.exists_polyhedralPL_parameter_transport K hK j hjK originalK
    (fun x => hvalue (p x))
  let moved : C(source, R) := (⟨G, G.continuous⟩ : C(R, R)).comp original
  have hnew (x : source) : g x = (G (original x) : X) := hgv (p.symm x)
  refine ⟨g, moved, hKs ▸ hg, isEmbedding_original_parameter_transport G j g original
    hvalue hnew hemb, rfl, hnew, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hnew, hfront, ← hvalue]
    exact hproper x
  · exact fun b => sourceAnnulusRim_nonnullhomotopic_comp_homeomorph G original b (hessential b)
  · intro x hx
    rw [hnew, hx, hvalue]
  · intro b hfix
    apply ContinuousMap.ext
    exact hfix
  · intro b z
    exact hnew ⟨(endpoint b, z), sphere_subset_closedBall (endpoint_mem_sphere b), z.property⟩

end Dehn.ProtectedAnnulus
end PoincareConjecture.M76
