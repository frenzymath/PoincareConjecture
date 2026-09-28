


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.OrientedGraphs
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseDirections
import Mathlib.Analysis.Calculus.Deriv.Prod









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold
open Poincare.Topology.Plane.Curves

namespace Poincare.Topology.Plane.Curves



theorem linear_graph_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (A : E ≃L[ℝ] (ℝ × ℝ)) (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hgraph : ∀ t ∈ G.source, A (f t) = (G t, h (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hf : DifferentiableAt ℝ f t) :
    A (deriv f t) = deriv G t • ((1 : ℝ), deriv h (G t)) := by
  have hdG := ((hG t ht).contDiffAt (G.open_source.mem_nhds ht)).differentiableAt (by simp)
  have hdh := ((hh (G t) (G.map_source ht)).contDiffAt
    (G.open_target.mem_nhds (G.map_source ht))).differentiableAt (by simp)
  have hdleft := A.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
  have hdright := hdG.hasDerivAt.prodMk (hdh.hasDerivAt.comp t hdG.hasDerivAt)
  have heq : (A ∘ f) =ᶠ[𝓝 t] (fun u => (G u, h (G u))) :=
    Filter.mem_of_superset (G.open_source.mem_nhds ht) (hgraph ·)
  have hderiv := hdleft.unique (hdright.congr_of_eventuallyEq heq)
  change A (deriv f t) = (deriv G t, deriv h (G t) * deriv G t) at hderiv
  rw [hderiv]
  ext <;> simp [smul_eq_mul, mul_comm]

end Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in



theorem exists_common_graph_transversal (e : D.EdgeIndex) (R : D.regions)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (A B : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G H : OpenPartialHomeomorph ℝ ℝ) (f g : ℝ → ℝ)
    (hG : ContDiffOn ℝ ∞ G G.source) (hH : ContDiffOn ℝ ∞ H H.source)
    (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
    (hAsource : ∀ x ∈ G.target, A.symm (x, f x) ∈ C.source)
    (hBsource : ∀ x ∈ H.target, B.symm (x, g x) ∈ C.source)
    (hAgraph : ∀ t ∈ G.source, (D.edge e.1 e.2).map t = C (A.symm (G t, f (G t))))
    (hBgraph : ∀ t ∈ H.source, (D.edge e.1 e.2).map t = C (B.symm (H t, g (H t))))
    {t : ℝ} (htG : t ∈ G.source) (htH : t ∈ H.source)
    (hprojectionA : 0 < (A (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)).1)
    (hprojectionB : 0 < (B (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)).1)
    {α β γ η δA δB : ℝ} (htA : G t ∈ Ioo α β) (htB : H t ∈ Ioo γ η)
    (hδA : 0 < δA) (hδB : 0 < δB)
    (hAtube : ∀ x ∈ Ioo α β, ∀ z : ℝ, |z| < δA →
      A.symm (x, f x + z) ∈ C.source ∧
      (C (A.symm (x, f x + z)) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z))
    (hBtube : ∀ x ∈ Ioo γ η, ∀ z : ℝ, |z| < δB →
      B.symm (x, g x + z) ∈ C.source ∧
      (C (B.symm (x, g x + z)) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z)) :
    ∃ (d : EuclideanSpace ℝ (Fin 2)) (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ),
      d = A.symm (0, 1) ∧ d ≠ 0 ∧
      ℓ = (ContinuousLinearMap.fst ℝ ℝ ℝ).comp A.toContinuousLinearMap ∧
      (A d).2 - deriv f (G t) * (A d).1 = 1 ∧
      0 < (B d).2 - deriv g (H t) * (B d).1 ∧
      ℓ d = 0 ∧
      0 < ℓ (A.symm (1, deriv f (G t))) ∧
      0 < ℓ (B.symm (1, deriv g (H t))) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        C.symm ((D.edge e.1 e.2).map t) + r • d ∈ C.source ∧
        C (C.symm ((D.edge e.1 e.2).map t) + r • d) ∈ connectedComponentIn
          (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  let c := C.symm ∘ (D.edge e.1 e.2).map
  let p := c t
  let v := deriv c t
  let d := A.symm ((0 : ℝ), (1 : ℝ))
  let ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp A.toContinuousLinearMap
  have hAcoord (u : ℝ) (hu : u ∈ G.source) : A (c u) = (G u, f (G u)) := by
    dsimp [c]
    rw [hAgraph u hu, C.left_inv (hAsource _ (G.map_source hu)), A.apply_symm_apply]
  have hBcoord (u : ℝ) (hu : u ∈ H.source) : B (c u) = (H u, g (H u)) := by
    dsimp [c]
    rw [hBgraph u hu, C.left_inv (hBsource _ (H.map_source hu)), B.apply_symm_apply]
  have hctarget : (D.edge e.1 e.2).map t ∈ C.target := by
    rw [hAgraph t htG]
    exact C.map_source (hAsource _ (G.map_source htG))
  have hc : DifferentiableAt ℝ c t :=
    ((D.edge_coordinate_contDiffOn e C hCinv t hctarget).contDiffAt
      ((C.open_target.preimage (D.edge_contMDiff e).continuous).mem_nhds hctarget)).differentiableAt
        (by simp)
  have hAv := linear_graph_tangent A G hG hf hAcoord htG hc
  have hBv := linear_graph_tangent B H hH hg hBcoord htH hc
  have hHpos : 0 < deriv H t := by
    have he := congrArg Prod.fst hBv
    simp only [Prod.smul_mk, smul_eq_mul, mul_one] at he
    exact he ▸ hprojectionB
  have hAp : A p = (G t, f (G t)) := hAcoord t htG
  have hBp : B p = (H t, g (H t)) := hBcoord t htH
  have hBp1 : (B p).1 = H t := congrArg Prod.fst hBp
  have hgp : DifferentiableAt ℝ g (B p).1 := by
    rw [hBp1]
    exact ((hg _ (H.map_source htH)).contDiffAt
      (H.open_target.mem_nhds (H.map_source htH))).differentiableAt (by simp)
  have hpgraph : (B p).2 = g (B p).1 := by rw [hBp]
  have hAd : (A d).2 - deriv f (G t) * (A d).1 = 1 := by simp [d]
  have hray (r : ℝ) : p + r • d = A.symm (G t, f (G t) + r) := by
    apply A.injective
    rw [map_add, map_smul, hAp, A.apply_symm_apply]
    simp
  let x : ℝ → ℝ := fun r => (B (p + r • d)).1
  let z : ℝ → ℝ := fun r => (B (p + r • d)).2 - g (x r)
  have hx : ContinuousAt x 0 := by dsimp [x]; fun_prop
  have hxzero : x 0 = H t := by simpa [x] using hBp1
  have hz : ContinuousAt z 0 := by
    have hgc : ContinuousAt g (x 0) := by simpa [x] using hgp.continuousAt
    have hbc : ContinuousAt (fun r : ℝ => (B (p + r • d)).2) 0 := by fun_prop
    exact hbc.sub (hgc.comp (f := x) hx)
  have hzzero : z 0 = 0 := by simp [z, x, hpgraph]
  have hxin : ∀ᶠ r in 𝓝 (0 : ℝ), x r ∈ Ioo γ η :=
    hx.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hxzero.symm ▸ htB))
  have hzin : ∀ᶠ r in 𝓝 (0 : ℝ), z r ∈ Ioo (-δB) δB :=
    hz.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hzzero]; exact ⟨by linarith, hδB⟩))
  have hrin : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ Ioo (-δA) δA :=
    isOpen_Ioo.mem_nhds ⟨by linarith, hδA⟩
  have hBpolar (r : ℝ) : p + r • d = B.symm (x r, g (x r) + z r) := by
    apply B.injective
    rw [B.apply_symm_apply]
    apply Prod.ext
    · rfl
    · dsimp [z]
      ring
  have hray_region : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (p + r • d ∈ C.source ∧ C (p + r • d) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ∧ 0 < z r := by
    filter_upwards [hxin.filter_mono nhdsWithin_le_nhds, hzin.filter_mono nhdsWithin_le_nhds,
      hrin.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hxr hzr hrr hrpos
    have hlocA := hAtube (G t) htA r (abs_lt.mpr hrr)
    have hR : C (p + r • d) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
      rw [hray]
      exact hlocA.2.mpr hrpos
    refine ⟨⟨hray r ▸ hlocA.1, hR⟩, ?_⟩
    apply (hBtube (x r) hxr (z r) (abs_lt.mpr hzr)).2.mp
    rw [← hBpolar]
    exact hR
  have hBv' : B v = deriv H t • ((1 : ℝ), deriv g (B p).1) := by
    rw [hBp1]
    exact hBv
  have htransB : 0 < (B d).2 - deriv g (H t) * (B d).1 := by
    rw [← hBp1]
    apply graph_transverse_pos_of_eventually_above A B (ne_of_gt hHpos) hAv hBv'
      (by rw [hAd]; norm_num) hgp hpgraph
    exact hray_region.mono (fun _ hr => hr.2)
  have hsepB : 0 < ℓ (B.symm (1, deriv g (H t))) := by
    have he := congrArg (fun y => ℓ (B.symm y)) hBv
    simp only [B.symm_apply_apply, map_smul, smul_eq_mul] at he
    exact (mul_pos_iff_of_pos_left hHpos).mp (he ▸ hprojectionA)
  refine ⟨d, ℓ, rfl, ?_, rfl, hAd, htransB, ?_, ?_, hsepB,
    hray_region.mono (fun _ hr => hr.1)⟩
  · intro hd
    have he := congrArg A hd
    simp [d] at he
  · simp [ℓ, d]
  · simp [ℓ]

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
