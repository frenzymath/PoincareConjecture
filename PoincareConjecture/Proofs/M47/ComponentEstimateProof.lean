import PoincareConjecture.Proofs.M47.ComponentEstimateFullHistory
import PoincareConjecture.Proofs.M47.ComponentEstimateEndpoint
import PoincareConjecture.Proofs.M47.ComponentEstimateNormalization
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientHomothety
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothety











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47




theorem componentAnalyticBounds
    (P : M47Predecessors.{u}) (PA : M47ComponentAnalyticPredecessors.{u})
    (C : ℝ) (hC : 1 ≤ C) : Nonempty (M47ComponentAnalyticBounds.{u} C) := by
  obtain ⟨d, hd, hd1, delta, hdelta, hhistory⟩ := exists_component_backward_duration P PA C hC
  let L := 4 * (C + 1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hK : 0 < 13 * L := by positivity
  obtain ⟨A, hA, hendpoint⟩ := exists_component_normalized_endpoint_constant P.m04 PA
    (d / 2) (13 * L) (half_pos hd) (by linarith) hK
  refine ⟨{
    duration := d
    duration_pos := hd
    duration_le_one := hd1
    curvature_threshold := max 6 (Real.exp 4)
    one_le_curvature_threshold := (by norm_num : (1 : ℝ) ≤ 6).trans (le_max_left _ _)
    constant := A
    constant_pos := hA
    delta := delta
    delta_pos := hdelta
    estimate := ?_
  }⟩
  intro g₀ K F hmodel hconstants _hparameter _hepsilon t Q x hxQ hthreshold
    htime hpinch hcanonical hcutoff N hx
  have hQ6 : 6 ≤ Q := (le_max_left _ _).trans hthreshold
  have hQexp : Real.exp 4 ≤ Q := (le_max_right _ _).trans hthreshold
  have hQ : 0 < Q := by linarith
  let : LocallyConnectedSpace (F.slice t).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (F.slice t).carrier
  have hopen : IsOpen N.carrier := by rw [N.component_eq]; exact isOpen_connectedComponent
  let U : TopologicalSpace.Opens (F.slice t).carrier := ⟨N.carrier, hopen⟩
  let : CompactSpace U := isCompact_iff_compactSpace.mp N.compact
  have hcutoff' : ∀ T ∈ Icc (t - d / Q) t, T ∈ F.surgery_times →
      F.parameters.delta T ≤ delta F.standard_initial F.local_constants := by
    intro T hT hS
    rw [hmodel, hconstants]
    exact hcutoff T hT hS
  obtain ⟨e, he, hscalar⟩ := hhistory F t Q x hxQ hQ6 hQexp htime hpinch hcanonical
    hcutoff' N hx U rfl
  obtain ⟨G, hcurvature, hmetric⟩ := exists_component_normalized_history P hd hQ hQexp hL
    U ⟨x, hx⟩ e he (fun s hs y => (hscalar s hs y).le) hpinch
  let z : U := ⟨x, hx⟩
  have hbounds := hendpoint U G hcurvature z
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (Subtype.val : U → (F.slice t).carrier) univ := contMDiff_subtype_val.contMDiffOn
  have hgrad := scalarGradientNorm_eq_of_local_homothety
    (G.connection (d / 2)) (F.connection t) hQ isOpen_univ hsmooth
    (fun y _hy => hmetric y) (x := z) (mem_univ z)
  have hevolution := (G.connection (d / 2)).scalarEvolutionNumerator_eq_of_local_homothety
    (F.connection t) hQ isOpen_univ hsmooth
    (fun y _hy => hmetric y) (x := z) (mem_univ z)
  have hgradBound : scalarGradientNorm (F.metric t) (F.connection t) x /
      Q ^ (3 / 2 : ℝ) ≤ A := hgrad.symm.trans_le hbounds.1
  have hevolutionBound : |((F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) / Q ^ 2| ≤ A := by
    rw [← hevolution]
    exact hbounds.2
  rw [abs_div, abs_of_pos (pow_pos hQ 2)] at hevolutionBound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hxQ] using hQ
  · rw [hxQ]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hQ _)).1 hgradBound
  · rw [hxQ]
    exact (div_le_iff₀ (pow_pos hQ 2)).1 hevolutionBound

end PoincareConjecture.M47
