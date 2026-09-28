import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem core_radius_lower_of_scalar_upper (N : CapCertificate g)
    {B : ℝ} (hB : 0 ≤ B) (hscalar : ∀ z ∈ N.carrier, N.connection.scalarCurvature z ≤ B)
    {y : M} (hy : y ∈ N.core) :
    (B + 1)⁻¹ ≤ N.core_radius y := by
  have hr := N.core_radius_pos y hy
  have hyball : y ∈ g.ball y (N.core_radius y) := by
    change g.edist y y < ENNReal.ofReal (N.core_radius y)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  let : Nonempty (g.ball y (N.core_radius y)) := ⟨⟨y, hyball⟩⟩
  have hsquare : (N.core_radius y)⁻¹ ^ 2 ≤ B := by
    rw [← N.core_radius_eq y hy]
    apply csSup_le (range_nonempty (fun z : g.ball y (N.core_radius y) =>
      N.connection.scalarCurvature z))
    rintro _ ⟨z, rfl⟩
    exact hscalar z (N.core_ball_subset y hy (subset_closure z.property))
  have hinv : (N.core_radius y)⁻¹ ≤ B + 1 := by
    nlinarith [sq_nonneg ((N.core_radius y)⁻¹ - 1)]
  have h := (inv_le_inv₀ (by positivity : 0 < B + 1) (inv_pos.mpr hr)).mpr hinv
  simpa only [inv_inv] using h

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_eventually_captured_cap_scalar_upper
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t), N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          (∀ z ∈ N.carrier, N.connection.scalarCurvature z ≤ B) ∧
          (∀ z ∈ N.carrier,
            (F.connection t).curvatureTensorNorm z ≤ 13 * max B (Real.exp 4)) ∧
          ∀ y ∈ N.core, (B + 1)⁻¹ ≤ N.core_radius y := by
  obtain ⟨b, hb⟩ := (hA.image
    (H.terminalConnection P04).continuous_scalarCurvature).bddAbove
  let B := max b 1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right b 1]
  refine ⟨B, hB, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) 1 zero_lt_one] with t hclose
  intro ht N hconnection hcapture
  have hscalar : ∀ z ∈ N.carrier, N.connection.scalarCurvature z ≤ B := by
    intro z hz
    obtain ⟨x, hx, hxeq⟩ := hcapture (mem_image_of_mem _ hz)
    have hf : H.reference.forward t ht x = z := by
      rw [hxeq]
      exact H.reference.right_inverse t ht z
    have hh := hclose x hx
    rw [Real.dist_eq, abs_sub_lt_iff] at hh
    have hbound := hb (mem_image_of_mem _ hx)
    have heq : N.connection.scalarCurvature z = H.reference.scalar t x := by
      rw [hconnection, ← hf]
      exact H.reference.scalar_pullback t ht x
    rw [heq]
    dsimp [B]
    linarith [le_max_left b 1]
  exact ⟨hscalar, fun z hz => H.curvature_norm_le_of_scalar_le P04
    (H.reference.window_subset ht) z (by simpa only [hconnection] using hscalar z hz),
    fun y hy => N.core_radius_lower_of_scalar_upper hB.le hscalar hy⟩

end PoincareConjecture.SingularTimeAssumptions
