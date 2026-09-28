import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.BranchCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.ClippedParameters









set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}



theorem Step.exists_planar_surface_parameterized_branch_chart
    (step : Step s t) (hK : K.faces.Finite)
    (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space => j x))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ frontier K.space)
    (a b : K.space) (hab : a ≠ b) (hpair : (step.projection ∘ step.inclusion ∘ j) a = (step.projection ∘ step.inclusion ∘ j) b)
    (haint : (step.projection ∘ step.inclusion ∘ j) a ∈ interior (s.projection ⁻¹' R))
    {W : Set s.Carrier} (hW : IsOpen W) (haW : (step.projection ∘ step.inclusion ∘ j) a ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3),
      j a ∈ w.left.source ∧ j b ∈ w.right.source ∧
      (step.projection ∘ step.inclusion ∘ j) a ∈ Q.source ∧ Q ((step.projection ∘ step.inclusion ∘ j) a) = 0 ∧
      Q.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' Q.source =
        (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∪
          (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∧
      (∀ y ∈ Q.source, y ∈ (step.projection ∘ step.inclusion) ''
        (j '' K.space ∩ w.left.source) ↔ (c (Q y)).2 = 0) ∧
      ∀ J : SimplicialComplex ℝ V3, J.faces.Finite → J.space ⊆ Q.target →
        ∃ (P : SimplicialComplex ℝ V3) (g : V3 → A) (v : V3 → V2),
          P.faces.Finite ∧ P.space = (w.right.trans Q) ''
            (j '' K.space ∩ (w.right.trans Q).source) ∩ J.space ∧
          FinitePiecewiseAffineOn g P.space ∧ MapsTo g P.space K.space ∧
          (∀ z ∈ P.space, j (g z) ∈ (w.right.trans Q).source ∧
            (w.right.trans Q) (j (g z)) = z) ∧
          (∀ z ∈ K.space, j z ∈ (w.right.trans Q).source →
            (w.right.trans Q) (j z) ∈ J.space →
              g ((w.right.trans Q) (j z)) = z) ∧
          FinitePiecewiseAffineOn v P.space ∧ InjOn v P.space ∧
          ∀ z ∈ P.space, z ∈ interior J.space → v z ∈ interior (v '' P.space) := by
  obtain ⟨w, c, Q, hal, hbr, haQ, hQzero, hQW, hQPL, hbranches, hwhole, hplane, _⟩ :=
    step.exists_planar_surface_branch_chart hK hj hji hproper a b hab hpair haint hW haW
  obtain ⟨q, F, hqs, hqval, hF, _⟩ := exists_planar_interior_source_parameters K.space b
  have hfit (x : K.space) (hx : j x ∈ (w.right.trans Q).source) : x ∈ q.source := by
    rw [hqs]
    change (x : A) ∈ interior K.space
    by_contra hn
    have hf := (hproper x x.property).mpr ⟨subset_closure x.property, hn⟩
    rw [step.frontier_preimage R] at hf
    have hpQ : (step.projection ∘ step.inclusion) (j x) ∈ Q.source :=
      (congrFun w.right_eq (j x)) ▸ hx.2
    exact hf.2 (hQW hpQ).2.1
  refine ⟨w, c, Q, hal, hbr, haQ, hQzero, hQW, hQPL, hbranches, hwhole, hplane, ?_⟩
  intro J hJ hJQ
  have hJright : J.space ⊆ (w.right.trans Q).target := by
    intro z hz
    refine ⟨hJQ hz, ?_⟩
    change Q.symm z ∈ w.right.target
    rw [w.right_target]
    exact (hQW (Q.map_target (hJQ hz))).2.2
  obtain ⟨P, g, v, hP, hPs, hg, hgK, hright, hleft, hv, hvi, _, hint⟩ :=
    exists_clipped_planar_source_parameter K hK hj
      (fun x hx y hy hxy => congrArg Subtype.val (hji.injective
        (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
      (w.right.trans Q) (fun k => (hbranches k).2) q (interior K.space) F
      hqs hqval hF hfit J hJ hJright
  exact ⟨P, g, v, hP, hPs, hg, hgK, hright, hleft, hv, hvi, hint⟩

end Geometry.OriginalPLTower

