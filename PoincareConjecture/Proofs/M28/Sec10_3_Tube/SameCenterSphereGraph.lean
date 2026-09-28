import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphIsotopy
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28




theorem central_sphere_subset_small_slab_of_capture
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / (256 * standardSpherePathCeiling + 1))
    (hcenter : N'.center = N.center) (hscale : N'.scale = N.scale)
    (hcapture : N'.central_sphere ⊆ N.carrier) :
    N'.central_sphere ⊆ N.region (-(N.epsilon⁻¹ / 32)) (N.epsilon⁻¹ / 32) := by
  have hP : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hinv : 256 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hsmall
    simpa only [one_div, inv_inv] using h
  have hcN := N.central_sphere_subset N.center_on_central_sphere
  have hc0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcN).mp N.center_on_central_sphere
  intro x hx
  obtain ⟨sigma, h0, h1, hsmooth, hsphere, hlength, _, _⟩ :=
    exists_central_sphere_shortcut N' N'.center_on_central_sphere hx
  have hpath : MapsTo sigma (Icc (0 : ℝ) 1) N.carrier :=
    fun t _ => hcapture (hsphere (mem_univ t))
  have hbound := (path_axial_displacement_le N zero_le_one
    hsmooth.contMDiffOn hpath).trans_lt hlength
  rw [h0, h1, hcenter, hc0, sub_zero, hscale] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hP) N.scale_pos)).mp hbound
  have hheight : |(N.coordinate_inverse x).2| < 8 * standardSpherePathCeiling := by
    nlinarith [N.scale_pos]
  have hnarrow : |(N.coordinate_inverse x).2| < N.epsilon⁻¹ / 32 := by
    linarith
  exact ⟨hcapture hx, (abs_lt.mp hnarrow).1, (abs_lt.mp hnarrow).2⟩





theorem exists_same_center_neck_sphere_graph_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        N'.center = N.center → N'.scale = N.scale →
          ∃ f : UnitTwoSphere → ℝ,
            ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
            (∀ p, |f p| < N.epsilon⁻¹ / 32) ∧
            N'.central_sphere = range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  obtain ⟨epsilonG, hGpos, hGsmall, hgraph⟩ := exists_buffered_neck_sphere_graph_accuracy.{u}
  have hP : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  refine ⟨min epsilonG (1 / (256 * standardSpherePathCeiling + 1)),
    lt_min hGpos (by positivity), (min_le_left _ _).trans hGsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' hN hN' hcenter hscale
  have hcN := N.central_sphere_subset N.center_on_central_sphere
  have hc0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcN).mp N.center_on_central_sphere
  obtain ⟨q, hq⟩ : ∃ q : UnitTwoSphere, N'.coordinate_map (q, 0) = N'.center := by
    have h := N'.center_on_central_sphere
    rw [← N'.centralSphere_range] at h
    exact h
  have hzero : (0 : ℝ) ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr N'.epsilon_pos), inv_pos.mpr N'.epsilon_pos⟩
  have hmeet : N'.coordinate_map (q, 0) ∈ N.carrier := by rw [hq, hcenter]; exact hcN
  have haxis : |(N.coordinate_inverse (N'.coordinate_map (q, 0))).2| ≤
      3 * N.epsilon⁻¹ / 4 := by
    rw [hq, hcenter, hc0, abs_zero]
    have hA := inv_pos.mpr N.epsilon_pos
    positivity
  obtain ⟨phi, _, f, hf, hbuffer, _, hrange⟩ := hgraph M g D N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _)) 0 hzero q hmeet haxis
  have hdom (p : UnitTwoSphere) : f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have h := abs_lt.mp (hbuffer p)
    have hA := inv_pos.mpr N.epsilon_pos
    constructor <;> linarith [h.1, h.2]
  have hsphere : N'.central_sphere =
      range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) :=
    N'.centralSphere_range.symm.trans hrange
  have hcapture : N'.central_sphere ⊆ N.carrier := by
    rw [hsphere]
    rintro _ ⟨p, rfl⟩
    exact N.coordinate_map_mem_of_axial _ (hdom p)
  have hsharp := central_sphere_subset_small_slab_of_capture N N'
    (hN.trans (min_le_right _ _)) hcenter hscale hcapture
  refine ⟨f, hf, ?_, hsphere⟩
  intro p
  have hx : N.coordinate_map (p, f p) ∈ N'.central_sphere :=
    hsphere.symm ▸ mem_range_self p
  have h := (hsharp hx).2
  rw [N.coordinate_inverse_coordinate_map_of_axial _ (hdom p)] at h
  exact abs_lt.mpr h

end PoincareConjecture.M28
