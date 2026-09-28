import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.CollarCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.TransverseLevels

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

theorem exists_smooth_coordinate_restriction
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ))
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ F.source)
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D) (hpD : p ∈ D)
    (hF : ContDiffOn ℝ ∞ F D)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (hd : HasFDerivAt F (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) p) :
    ∃ G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ),
      p ∈ G.source ∧ (∀ z, G z = F z) ∧ G.source ⊆ D ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target := by
  have hfAt := hF.contDiffAt (hD.mem_nhds hpD)
  have hInv : (fderiv ℝ F) ⁻¹'
      range (fun e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ) =>
        (e : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ))) ∈ 𝓝 p := by
    apply (hfAt.continuousAt_fderiv (by simp)).preimage_mem_nhds
    rw [hd.fderiv]
    exact L.nhds
  obtain ⟨V, hVsub, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hInv
  let G := F.restrOpen (D ∩ V) (hD.inter hVopen)
  have hGD : G.source ⊆ D := fun _ hz => hz.2.1
  refine ⟨G, ⟨hp, hpD, hpV⟩, fun _ => rfl, hGD, hF.mono hGD, ?_⟩
  intro q hq
  have hqsource := G.map_target hq
  have hqAt : ContDiffAt ℝ ∞ F (G.symm q) :=
    hF.contDiffAt (hD.mem_nhds (hGD hqsource))
  obtain ⟨A, hA⟩ := hVsub hqsource.2.2
  change (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) = fderiv ℝ F (G.symm q) at hA
  apply (G.contDiffAt_symm (f₀' := A) hq ?_ hqAt).contDiffWithinAt
  change HasFDerivAt F (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) (G.symm q)
  rw [hA]
  exact (hqAt.differentiableAt (by simp)).hasFDerivAt

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem exists_chartCircle_crossing_coordinates (x y : M) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) rx ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hysub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) y y) ry ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).target)
    {p : M} (hpx : p ∈ chartCircle x rx) (hpy : p ∈ chartCircle y ry)
    (hregular : ChartCircleRegularAlong x rx y ry) :
    ∃ C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M,
      p ∈ C.target ∧
      C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) y).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      C.symm p = collarParameterEquiv.symm (ry ^ 2, rx ^ 2) ∧
      (∀ z ∈ C.source,
        ‖chartAt (EuclideanSpace ℝ (Fin 2)) y (C z) -
          chartAt (EuclideanSpace ℝ (Fin 2)) y y‖ ^ 2 = z 0 ∧
        ‖chartAt (EuclideanSpace ℝ (Fin 2)) x (C z) -
          chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 = z 1) ∧
      (∀ z ∈ C.source, C z ∈ chartCircle y ry ↔ z 0 = ry ^ 2) ∧
      (∀ z ∈ C.source, C z ∈ chartCircle x rx ↔ z 1 = rx ^ 2) := by
  let ex := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let ey := chartAt (EuclideanSpace ℝ (Fin 2)) y
  let D := (ey.symm.trans ex).source
  let f := fun w : EuclideanSpace ℝ (Fin 2) => ‖w - ey y‖ ^ 2
  let g := fun w : EuclideanSpace ℝ (Fin 2) => ‖ex (ey.symm w) - ex x‖ ^ 2
  have hpsx := chartCircle_subset_chart_source x hxsub hpx
  have hpsy := chartCircle_subset_chart_source y hysub hpy
  have hpD : ey p ∈ D := by
    refine ⟨ey.map_source hpsy, ?_⟩
    change ey.symm (ey p) ∈ ex.source
    rwa [ey.left_inv hpsy]
  have htransition : ContDiffOn ℝ ∞ (ex ∘ ey.symm) D := by
    have h := (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x)).comp
      ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := y)).mono
        (show D ⊆ ey.target from fun _ hz => hz.1)) (fun _ hz => hz.2)
    exact h.contDiffOn
  have hfOn : ContDiffOn ℝ ∞ f D :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hgOn : ContDiffOn ℝ ∞ g D :=
    (contDiff_norm_sq ℝ).comp_contDiffOn (htransition.sub contDiffOn_const)
  obtain ⟨hfval, hgval, hf, hg, hdf, v, hvf, hvg⟩ :=
    chartCircle_pair_coordinate_derivatives x y hrx hry hxsub hysub hpx hpy hregular
  obtain ⟨F, hpF, hF, _, _⟩ :=
    Poincare.Topology.Plane.Curves.exists_local_coordinates_of_transverse_levels hf hg hdf hvf hvg
  have hFeq : (F : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun w => (f w, g w) := funext hF
  have hFOn : ContDiffOn ℝ ∞ F D := by
    rw [hFeq]
    exact hfOn.prodMk hgOn
  obtain ⟨A, hA⟩ :=
    Poincare.Topology.Plane.Curves.exists_equiv_of_transverse_functionals hdf hvf hvg
  have hdF : HasFDerivAt F (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) (ey p) := by
    rw [hFeq]
    convert! ((hf.differentiableAt (by simp)).hasFDerivAt).prodMk
      ((hg.differentiableAt (by simp)).hasFDerivAt) using 1
    exact ContinuousLinearMap.ext hA
  obtain ⟨G, hpG, hGmap, hGD, hG, hGinv⟩ :=
    exists_smooth_coordinate_restriction F hpF (ey.symm.trans ex).open_source hpD hFOn A hdF
  let L := collarParameterEquiv
  let H := L.toHomeomorph.toOpenPartialHomeomorph.trans G.symm
  let C := H.trans ey.symm
  have hH : ContDiffOn ℝ ∞ H H.source :=
    hGinv.comp L.contDiff.contDiffOn (fun _ hz => hz.2)
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target :=
    L.symm.contDiff.comp_contDiffOn (hG.mono (fun _ hz => hz.1))
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := y)).comp
      (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    hHinv.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := y)).mono (fun _ hz => hz.1))
      (fun _ hz => hz.2)
  have hCtarget : C.target ⊆ ex.source ∩ ey.source := by
    intro q hq
    refine ⟨?_, hq.1⟩
    have h := (hGD hq.2.1).2
    change ey.symm (ey q) ∈ ex.source at h
    rwa [ey.left_inv hq.1] at h
  have hcoords (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ C.source) :
      ‖ey (C z) - ey y‖ ^ 2 = z 0 ∧ ‖ex (C z) - ex x‖ ^ 2 = z 1 := by
    have h := G.right_inv hz.1.2
    rw [hGmap, hF] at h
    have hpair : f (G.symm (L z)) = z 0 ∧ g (G.symm (L z)) = z 1 :=
      Prod.mk.inj h
    constructor
    · change ‖ey (ey.symm (G.symm (L z))) - ey y‖ ^ 2 = z 0
      rw [ey.right_inv (show G.symm (L z) ∈ ey.target from hz.2)]
      exact hpair.1
    · exact hpair.2
  refine ⟨C, ⟨hpsy, hpG, mem_univ _⟩, hCtarget, hC, hCinv, ?_, hcoords, ?_, ?_⟩
  · change L.symm (G (ey p)) = L.symm (ry ^ 2, rx ^ 2)
    rw [hGmap, hF]
    exact congrArg L.symm (Prod.ext hfval hgval)
  · intro z hz
    rw [mem_chartCircle_iff_norm_sq y hry hysub (hCtarget (C.map_source hz)).2,
      (hcoords z hz).1]
  · intro z hz
    rw [mem_chartCircle_iff_norm_sq x hrx hxsub (hCtarget (C.map_source hz)).1,
      (hcoords z hz).2]

end PoincareConjecture.Topology.Surface
