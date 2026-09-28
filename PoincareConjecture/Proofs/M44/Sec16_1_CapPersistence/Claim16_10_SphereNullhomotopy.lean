import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereTopology
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StandardPatchChart
import PoincareConjecture.Proofs.M36.StandardBalls
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal ContinuousMap

namespace PoincareConjecture.M44

theorem StandardCylinderPatch.contMDiff_sphere {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun z : UnitTwoSphere => N.coordinate (z, 0)) := by
  intro z
  have hz : (z, (0 : ℝ)) ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ _, neg_neg_of_pos N.length_pos, N.length_pos⟩
  exact (N.coordinate_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).comp z
    (contMDiffAt_id.prodMk contMDiffAt_const)

def StandardCylinderPatch.sphereMap {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) : C(UnitTwoSphere, StandardCapSpace) :=
  ⟨fun z => N.coordinate (z, 0), (StandardCylinderPatch.contMDiff_sphere N).continuous⟩

theorem exists_standard_ball_containing_compact (g0 : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ A < R ∧ K ⊆ g0.metric.ball 0 R := by
  have hc : Continuous (fun y : StandardCapSpace => M36.radialArclength g0 ‖y‖) :=
    (M36.radialArclength_contDiff g0).continuous.comp continuous_norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc.continuousOn
  let R := max 0 (max A B) + 1
  have hR : 0 < R := by dsimp [R]; linarith only [le_max_left (0 : ℝ) (max A B)]
  have hAR : A < R := by
    dsimp [R]
    linarith only [(le_max_left A B).trans (le_max_right (0 : ℝ) (max A B))]
  refine ⟨R, hR, hAR, ?_⟩
  intro y hy
  change g0.metric.edist 0 y < ENNReal.ofReal R
  rw [M36.standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff hR]
  have hb := hB (mem_image_of_mem _ hy)
  have hBR := (le_max_right A B).trans (le_max_right (0 : ℝ) (max A B))
  dsimp only [R]
  linarith only [hb, hBR]

theorem StandardCylinderPatch.exists_sphere_ball {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (g0 : StandardInitialMetric) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ A < R ∧
      ∀ z : UnitTwoSphere, N.coordinate (z, 0) ∈ g0.metric.ball 0 R := by
  obtain ⟨R, hR, hAR, hsub⟩ := exists_standard_ball_containing_compact g0
    (isCompact_range (StandardCylinderPatch.sphereMap N).continuous) A
  exact ⟨R, hR, hAR, fun z => hsub (mem_range_self z)⟩

theorem standard_ball_contractible (g0 : StandardInitialMetric) {R : ℝ} (hR : 0 < R) :
    ContractibleSpace (g0.metric.ball 0 R) := by
  rw [M36.standard_ball_eq_euclidean g0 hR]
  exact (convex_ball (0 : StandardCapSpace) _).contractibleSpace
    ⟨0, Metric.mem_ball_self ((M36.radialEuclideanRadius_pos_iff g0 R).mpr hR)⟩

theorem sphere_factor_through_standard_ball_not_localHomeomorph
    (g0 : StandardInitialMetric) {R : ℝ} (hR : 0 < R)
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(UnitTwoSphere, g0.metric.ball 0 R)) (g : C(g0.metric.ball 0 R, X)) :
    ¬ IsLocalHomeomorph (g.comp f) := by
  let : ContractibleSpace (g0.metric.ball 0 R) := standard_ball_contractible g0 hR
  have hf : f.Nullhomotopic := (id_nullhomotopic (g0.metric.ball 0 R)).comp_left f
  intro hlocal
  exact sphere_localHomeomorph_not_nullhomotopic (g.comp f) hlocal (hf.comp_right g)

end PoincareConjecture.M44
