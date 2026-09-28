import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckAxialLength
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_neck_overlap_scale_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        (N.carrier ∩ N'.carrier).Nonempty →
        N.scale < 2 * N'.scale ∧ N'.scale < 2 * N.scale := by
  obtain ⟨epsilon₀, hpos, hsmall, hscalar⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 4) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D N N' hN hN' hmeet
  obtain ⟨y, hy, hy'⟩ := hmeet
  have hleft := abs_lt.mp (hscalar M g D N hN y hy)
  have hright := abs_lt.mp (hscalar M g D N' hN' y hy')
  have hprod : 0 < N.scale ^ 2 * D.scalarCurvature y := by linarith
  have hR : 0 < D.scalarCurvature y := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact (not_lt_of_ge (sq_nonneg N.scale) h.1).elim
  have hscale : N.scale ^ 2 < 4 * N'.scale ^ 2 := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    nlinarith [hleft.2, hright.1]
  have hscale' : N'.scale ^ 2 < 4 * N.scale ^ 2 := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    nlinarith [hright.2, hleft.1]
  constructor <;> nlinarith [N.scale_pos, N'.scale_pos]

private theorem sphereSlice_subset_buffer_of_scale_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
    (N N' : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / (256 * standardSpherePathCeiling + 1))
    (hscale : N'.scale ≤ 2 * N.scale)
    {a : ℝ} (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (q : UnitTwoSphere) (hy : N'.coordinate_map (q, a) ∈ N.carrier)
    (haxis : |(N.coordinate_inverse (N'.coordinate_map (q, a))).2| ≤
      3 * N.epsilon⁻¹ / 4) :
    range (fun p : UnitTwoSphere => N'.coordinate_map (p, a)) ⊆
      N.region (-(7 * N.epsilon⁻¹ / 8)) (7 * N.epsilon⁻¹ / 8) := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hLs : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hlo : -N.epsilon⁻¹ < -(13 * N.epsilon⁻¹ / 16) := by linarith
  have hhi : 13 * N.epsilon⁻¹ / 16 < N.epsilon⁻¹ := by linarith
  have hinv : 256 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hsmall
    simpa only [one_div, inv_inv] using h
  rintro x ⟨p, rfl⟩
  have hcapture : N'.coordinate_map (p, a) ∈ N.coordinate_map ''
      (univ ×ˢ Icc (-(13 * N.epsilon⁻¹ / 16)) (13 * N.epsilon⁻¹ / 16)) := by
    by_contra hout
    obtain ⟨γ, hγ0, hγ1, hγ, hγlen, _, _⟩ := exists_standardSphere_short_path q p
    let η : ℝ → M := fun t => N'.coordinate_map (γ t, a)
    have hη : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 η := by
      rw [← contMDiffOn_univ]
      apply (N'.coordinate_map_smooth.of_le (by simp)).comp
      · exact (hγ.prodMk contMDiff_const).contMDiffOn
      · intro t _
        exact ⟨mem_univ _, ha⟩
    have h0 : η 0 = N'.coordinate_map (q, a) := by simp only [η, hγ0]
    have h1 : η 1 = N'.coordinate_map (p, a) := by simp only [η, hγ1]
    have hstart : η 0 ∈
        N.region (-(13 * N.epsilon⁻¹ / 16)) (13 * N.epsilon⁻¹ / 16) := by
      rw [h0]
      exact ⟨hy, by linarith [(abs_le.mp haxis).1],
        by linarith [(abs_le.mp haxis).2]⟩
    obtain ⟨t, ht, hprefix, hboundary, _⟩ :=
      N.exists_initial_segment_to_slab_boundary zero_le_one hlo hhi
        hη.continuous.continuousOn hstart (by simpa only [h1] using hout)
    have hterminal : |(N.coordinate_inverse (η t)).2| = 13 * N.epsilon⁻¹ / 16 := by
      rcases hboundary with hnegative | hpositive
      · rw [hnegative, abs_neg, abs_of_pos (by positivity)]
      · rw [hpositive, abs_of_pos (by positivity)]
    have hbegin : |(N.coordinate_inverse (η 0)).2| ≤ 3 * N.epsilon⁻¹ / 4 := by
      simpa only [h0] using haxis
    have htriangle := abs_sub_abs_le_abs_sub
      (N.coordinate_inverse (η t)).2 (N.coordinate_inverse (η 0)).2
    rw [hterminal] at htriangle
    have hgap : N.epsilon⁻¹ / 16 ≤
        |(N.coordinate_inverse (η t)).2 - (N.coordinate_inverse (η 0)).2| := by
      linarith
    have hgapScaled : N.scale * N.epsilon⁻¹ / 32 ≤
        (N.scale / 2) *
          |(N.coordinate_inverse (η t)).2 - (N.coordinate_inverse (η 0)).2| := by
      have h := mul_le_mul_of_nonneg_left hgap N.scale_pos.le
      nlinarith
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hpay : ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 32) ≤
        g.pathELength η 0 1 :=
      (ENNReal.ofReal_le_ofReal hgapScaled).trans
        ((path_axial_displacement_le N ht.1.le hη.contMDiffOn hprefix).trans
          (Manifold.pathELength_mono le_rfl ht.2))
    have hlength : g.pathELength η 0 1 <
        ENNReal.ofReal ((4 * standardSpherePathCeiling) * N'.scale) := by
      have hs : 0 < 4 * N'.scale := mul_pos (by norm_num) N'.scale_pos
      have hbound := (coordinate_sphere_pathELength_le N' hγ ha 0 1).trans_lt
        (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hs))
          ENNReal.ofReal_ne_top hγlen)
      convert hbound using 1
      rw [← ENNReal.ofReal_mul hs.le]
      congr 1
      ring
    have hbudget : (4 * standardSpherePathCeiling) * N'.scale ≤
        N.scale * N.epsilon⁻¹ / 32 := by
      have hfirst := mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hLs.le)
      have hsecond := mul_le_mul_of_nonneg_left hinv N.scale_pos.le
      nlinarith [N.scale_pos]
    exact (not_lt_of_ge hpay)
      (hlength.trans_le (ENNReal.ofReal_le_ofReal hbudget))
  have hcoords := (N.mem_coordinate_slab_iff hlo hhi).mp hcapture
  exact ⟨hcoords.1, by linarith [hcoords.2.1], by linarith [hcoords.2.2]⟩

theorem exists_buffered_neck_sphere_capture_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        ∀ a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹, ∀ q : UnitTwoSphere,
          N'.coordinate_map (q, a) ∈ N.carrier →
          |(N.coordinate_inverse (N'.coordinate_map (q, a))).2| ≤
            3 * N.epsilon⁻¹ / 4 →
          range (fun p : UnitTwoSphere => N'.coordinate_map (p, a)) ⊆
            N.region (-(7 * N.epsilon⁻¹ / 8)) (7 * N.epsilon⁻¹ / 8) := by
  obtain ⟨epsilonS, hSpos, hSsmall, hscale⟩ := exists_neck_overlap_scale_accuracy.{u}
  let epsilon₀ := min epsilonS (1 / (256 * standardSpherePathCeiling + 1))
  have hLs : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hpos : 0 < epsilon₀ := lt_min hSpos (by positivity)
  refine ⟨epsilon₀, hpos, (min_le_left _ _).trans hSsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' hN hN' a ha q hy haxis
  have hratio := hscale M g D N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _))
    ⟨N'.coordinate_map (q, a), hy, N'.coordinate_map_mem_of_axial (q, a) ha⟩
  exact sphereSlice_subset_buffer_of_scale_le N N'
    (hN.trans (min_le_right _ _)) hratio.2.le ha q hy haxis

end PoincareConjecture.M28
