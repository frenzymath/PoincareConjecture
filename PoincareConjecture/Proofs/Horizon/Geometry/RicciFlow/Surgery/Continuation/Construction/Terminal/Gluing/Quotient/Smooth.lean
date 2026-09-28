import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Quotient.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Gluing.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gluing.Compatibility








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Manifold IsManifold
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {P : ι → Type v} [∀ i, TopologicalSpace (P i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  [∀ i, IsManifold (𝓡 3) ∞ (P i)]
  (O : Poincare.Gluing.OverlapSystem P)
  (hs : ∀ i j, ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (O.transition i j) (O.transition i j).source)

include hs

theorem isManifold :
    letI := chartedSpace O
    IsManifold (𝓡 3) ∞ (Quotient O.setoid) := by
  let := chartedSpace O
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  have hcomp : ContDiffOn ℝ ∞
      (fun x => chartAt (EuclideanSpace ℝ (Fin 3)) b.2
        (O.transition a.1 b.1 ((chartAt (EuclideanSpace ℝ (Fin 3)) a.2).symm x)))
      ((liftedChart O a).symm.trans (liftedChart O b)).source := by
    intro x hx
    obtain ⟨hxa, hxb, _⟩ := liftedChart_transition O a b hx
    have hxt : x ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) a.2).target := hx.1
    have ha := (contMDiffOn_symm_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := 𝓡 3) (n := ∞) a.2)).contMDiffAt
        ((chartAt (EuclideanSpace ℝ (Fin 3)) a.2).open_target.mem_nhds hxt)
    have ht := (hs a.1 b.1).contMDiffAt
      ((O.transition a.1 b.1).open_source.mem_nhds hxa)
    have hb := (contMDiffOn_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := 𝓡 3) (n := ∞) b.2)).contMDiffAt
        ((chartAt (EuclideanSpace ℝ (Fin 3)) b.2).open_source.mem_nhds hxb)
    exact ((hb.comp x (ht.comp x ha)).contDiffAt).contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ ((liftedChart O a).symm.trans (liftedChart O b))
      ((liftedChart O a).symm.trans (liftedChart O b)).source :=
    hcomp.congr (fun x hx => (liftedChart_transition O a b hx).2.2)
  simpa only [mfld_simps] using hc

theorem include_isLocalDiffeomorph (i : ι) :
    letI := chartedSpace O
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (O.include i) := by
  let := chartedSpace O
  let := isManifold O hs
  intro x
  let e := chartAt (EuclideanSpace ℝ (Fin 3)) x
  let c := liftedChart O ⟨i, x⟩
  have he : e ∈ maximalAtlas (𝓡 3) ∞ (P i) := chart_mem_maximalAtlas x
  have hc : c ∈ maximalAtlas (𝓡 3) ∞ (Quotient O.setoid) :=
    subset_maximalAtlas ⟨⟨i, x⟩, rfl⟩
  let de : PartialDiffeomorph (𝓡 3) (𝓡 3) (P i)
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  let dc : PartialDiffeomorph (𝓡 3) (𝓡 3) (Quotient O.setoid)
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  refine ⟨de.trans dc.symm, ?_, ?_⟩
  · exact ⟨mem_chart_source _ x, e.map_source (mem_chart_source _ x)⟩
  · intro y hy
    change O.include i y = O.include i (e.symm (e y))
    rw [e.left_inv hy.1]

end PoincareConjecture.Surgery.Terminal.Gluing
