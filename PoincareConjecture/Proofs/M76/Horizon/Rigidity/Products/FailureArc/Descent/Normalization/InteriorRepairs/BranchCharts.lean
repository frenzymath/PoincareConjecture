import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.SourceParameters
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProjectedDoubleLocus
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProjectedEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialAnnulus
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows
import PoincareConjecture.Proofs.M76.Dehn.OriginalPairedRegionCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}

variable {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}



theorem Step.exists_planar_surface_branch_chart
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
        ∃ (P : SimplicialComplex ℝ V3) (g : V3 → A), P.faces.Finite ∧
          P.space = (w.right.trans Q) ''
            (j '' K.space ∩ (w.right.trans Q).source) ∩ J.space ∧
          FinitePiecewiseAffineOn g P.space ∧ InjOn g P.space ∧
          MapsTo g P.space K.space ∧
          (∀ z ∈ P.space, j (g z) ∈ (w.right.trans Q).source ∧
            (w.right.trans Q) (j (g z)) = z) ∧
          ∀ z ∈ K.space, j z ∈ (w.right.trans Q).source →
            (w.right.trans Q) (j z) ∈ J.space →
              g ((w.right.trans Q) (j z)) = z := by
  let p := step.projection ∘ step.inclusion
  have hp : Continuous p := step.projection.continuous.comp step.inclusion.continuous
  have hsourceint : (a : A) ∈ interior K.space := by
    by_contra hn
    have hf := (hproper a a.property).mpr ⟨subset_closure a.property, hn⟩
    rw [step.frontier_preimage R] at hf
    exact hf.2 haint
  obtain ⟨w, hal, hbr⟩ := step.projectionInclusion_local.exists_twoBranchWindow
    (fun z ↦ (step.projectionInclusion_fiber z).1)
    (fun z ↦ (step.projectionInclusion_fiber z).2) hpair
    (fun h ↦ hab (hji.injective h))
  obtain ⟨k, hak⟩ := t.cover (j a)
  let V := w.left.source ∩ p ⁻¹' (W ∩ interior (s.projection ⁻¹' R))
  have hV : IsOpen V := w.left.open_source.inter
    ((hW.inter isOpen_interior).preimage hp)
  obtain ⟨H, haH, hHV, _, hHz, hplane, hHPL⟩ :=
    exists_embedded_planar_interior_chart K hK hj
      hji (t.charts k) (fun l ↦ t.compatible l k)
      a hsourceint hak hV ⟨hal, haW, haint⟩
  let c : V3 ≃L[ℝ] C3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let T := H.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
  have hTPL (l : t.Index) : (t.charts l).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (locallyPiecewiseAffineOn_affine c.symm.toContinuousLinearMap.toContinuousAffineMap
      isOpen_univ).comp (hHPL l).1
    exact h.mono ((t.charts l).symm.trans T).open_source
      (fun z hz ↦ ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  let Q := w.left.symm.trans T
  have hleft (x : t.Carrier) (hx : x ∈ w.left.source) : w.left.symm (p x) = x :=
    (congrArg w.left.symm (congrFun w.left_eq x)).symm.trans (w.left.left_inv hx)
  have hproj (y : s.Carrier) (hy : y ∈ w.left.target) : p (w.left.symm y) = y :=
    (congrFun w.left_eq (w.left.symm y)).symm.trans (w.left.right_inv hy)
  have haQ : (step.projection ∘ step.inclusion ∘ j) a ∈ Q.source := by
    refine ⟨?_, ?_⟩
    · change (step.projection ∘ step.inclusion) (j a) ∈ w.left.target
      exact (congrFun w.left_eq (j a)) ▸ w.left.map_source hal
    · change w.left.symm (p (j a)) ∈ T.source
      rw [hleft _ hal]
      exact ⟨haH, mem_univ _⟩
  have hQW : Q.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) := by
    intro y hy
    have h := (hHV hy.2.1).1.2
    change p (w.left.symm y) ∈ W ∩ interior (s.projection ⁻¹' R) at h
    rw [hproj y hy.1] at h
    exact ⟨h.1, h.2, w.left_target.subset hy.1⟩
  have hQPL (l : s.Index) : (s.charts l).symm.trans Q ∈ piecewiseAffineGroupoid V3 :=
    (inverse_branch_chart_PL step) w.left (fun z _ ↦ congrFun w.left_eq z) T k
      (fun _ hz ↦ (hHV hz.1).2) (hTPL k) l
  have hbranch (l : t.Index) :
      (t.charts l).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
      (t.charts l).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3 :=
    ⟨step.compatible_branch_chart w.left (fun z _ ↦ congrFun w.left_eq z) Q hQPL l,
      step.compatible_branch_chart w.right (fun z _ ↦ congrFun w.right_eq z) Q hQPL l⟩
  refine ⟨w, c, Q, hal, hbr, haQ, ?_, hQW, hQPL, hbranch, ?_, ?_, ?_⟩
  · change c.symm (H (w.left.symm (p (j a)))) = 0
    rw [hleft _ hal, hHz, map_zero]
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQW hx).2.2 with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx ↦ hx.elim And.right And.right
  · intro y hy
    have hmem : y ∈ p '' (j '' K.space ∩ w.left.source) ↔
        w.left.symm y ∈ j '' K.space := by
      constructor
      · rintro ⟨x, ⟨hxK, hxL⟩, rfl⟩
        rwa [hleft _ hxL]
      · intro hx
        exact ⟨w.left.symm y, ⟨hx, w.left.map_target hy.1⟩, hproj _ hy.1⟩
    have hc : c (Q y) = H (w.left.symm y) := c.apply_symm_apply _
    rw [hc]
    exact hmem.trans (hplane _ hy.2.1)
  · intro J hJ hJQ
    have hJright : J.space ⊆ (w.right.trans Q).target := by
      intro z hz
      refine ⟨hJQ hz, ?_⟩
      change Q.symm z ∈ w.right.target
      rw [w.right_target]
      exact (hQW (Q.map_target (hJQ hz))).2.2
    obtain ⟨P, g, hP, hPs, hg, hgK, hright, hvalue⟩ :=
      hj.exists_finite_clipped_chart_inverse K hK
        (fun x hx y hy hxy ↦ congrArg Subtype.val (hji.injective
          (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
        (w.right.trans Q) (fun l ↦ (hbranch l).2) J hJ hJright
    refine ⟨P, g, hP, hPs, hg, ?_, hgK, hright, hvalue⟩
    intro z hz v hv hgv
    exact (hright z hz).2.symm.trans ((congrArg ((w.right.trans Q) ∘ j) hgv).trans
      (hright v hv).2)

end Geometry.OriginalPLTower
