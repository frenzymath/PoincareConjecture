import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.EmbeddedCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.ExceptionSchedule
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}

namespace OriginalRelativeNormalization

variable {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}



theorem exists_annulus_branch_chart
    (D : OriginalRelativeNormalization step K j R Rim)
    (hK : K.faces.Finite) (hKs : K.space = ProtectedAnnulus.source)
    (a b : K.space) (hab : a ≠ b) (hpair : D.projected a = D.projected b)
    {W : Set s.Carrier} (hW : IsOpen W) (haW : D.projected a ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3),
      D.endpoint a ∈ w.left.source ∧ D.endpoint b ∈ w.right.source ∧
      D.projected a ∈ Q.source ∧ Q (D.projected a) = 0 ∧
      Q.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' Q.source =
        (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∪
          (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∧
      (∀ y ∈ Q.source, y ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' K.space ∩ w.left.source) ↔ (c (Q y)).2 = 0) ∧
      ∀ J : SimplicialComplex ℝ V3, J.faces.Finite → J.space ⊆ Q.target →
        ∃ (P : SimplicialComplex ℝ V3) (g : V3 → A), P.faces.Finite ∧
          P.space = (w.right.trans Q) ''
            (D.endpoint '' K.space ∩ (w.right.trans Q).source) ∩ J.space ∧
          FinitePiecewiseAffineOn g P.space ∧ InjOn g P.space ∧
          MapsTo g P.space K.space ∧
          (∀ z ∈ P.space, D.endpoint (g z) ∈ (w.right.trans Q).source ∧
            (w.right.trans Q) (D.endpoint (g z)) = z) ∧
          ∀ z ∈ K.space, D.endpoint z ∈ (w.right.trans Q).source →
            (w.right.trans Q) (D.endpoint z) ∈ J.space →
              g ((w.right.trans Q) (D.endpoint z)) = z := by
  let p := step.projection ∘ step.inclusion
  have hp : Continuous p := step.projection.continuous.comp step.inclusion.continuous
  have hne : (a : A) ≠ b := fun h ↦ hab (Subtype.ext h)
  have haint := D.double_point_interior a.property b.property hne hpair
  have harim : (a : A).1 ∉ sphere (0 : V1) 1 := by
    intro h
    have haRim : (a : A) ∈ Rim := ⟨h, (hKs.subset a.property).2⟩
    exact ((D.projected_proper a a.property).mpr haRim).2 haint
  obtain ⟨w, hal, hbr⟩ := step.projectionInclusion_local.exists_twoBranchWindow
    (fun z ↦ (step.projectionInclusion_fiber z).1)
    (fun z ↦ (step.projectionInclusion_fiber z).2) hpair
    (fun h ↦ hab (D.endpoint_embedding.injective h))
  obtain ⟨k, hak⟩ := t.cover (D.endpoint a)
  let V := w.left.source ∩ p ⁻¹' (W ∩ interior (s.projection ⁻¹' R))
  have hV : IsOpen V := w.left.open_source.inter
    ((hW.inter isOpen_interior).preimage hp)
  obtain ⟨H, haH, hHV, _, hHz, hplane, hHPL⟩ :=
    ProtectedAnnulus.exists_embedded_interior_chart K hK hKs D.endpoint_PL
      D.endpoint_embedding (t.charts k) (fun l ↦ t.compatible l k)
      a harim hak hV ⟨hal, haW, haint⟩
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
  have haQ : D.projected a ∈ Q.source := by
    refine ⟨?_, ?_⟩
    · change (step.projection ∘ step.inclusion) (D.endpoint a) ∈ w.left.target
      exact (congrFun w.left_eq (D.endpoint a)) ▸ w.left.map_source hal
    · change w.left.symm (p (D.endpoint a)) ∈ T.source
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
  · change c.symm (H (w.left.symm (p (D.endpoint a)))) = 0
    rw [hleft _ hal, hHz, map_zero]
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQW hx).2.2 with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx ↦ hx.elim And.right And.right
  · intro y hy
    have hmem : y ∈ p '' (D.endpoint '' K.space ∩ w.left.source) ↔
        w.left.symm y ∈ D.endpoint '' K.space := by
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
      D.endpoint_PL.exists_finite_clipped_chart_inverse K hK
        (fun x hx y hy hxy ↦ congrArg Subtype.val (D.endpoint_embedding.injective
          (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
        (w.right.trans Q) (fun l ↦ (hbranch l).2) J hJ hJright
    refine ⟨P, g, hP, hPs, hg, ?_, hgK, hright, hvalue⟩
    intro z hz v hv hgv
    exact (hright z hz).2.symm.trans ((congrArg ((w.right.trans Q) ∘ D.endpoint) hgv).trans
      (hright v hv).2)

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
