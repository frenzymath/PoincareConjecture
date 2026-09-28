import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LocalSideUniqueness
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength
import PoincareConjecture.Proofs.M58.Sec18_4_UniformRadius












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}





theorem m64MinimizingSide_normalized_geodesic {ell : ℝ} (hell : 0 < ell)
    {p q : M} (side : M63MinimizingGeodesicSide g D ell p q) :
    g.IsGeodesicOn (fun t => side.map (ell * t)) (Icc (0 : ℝ) 1) := by
  intro t ht
  apply (m64MinimizingSide_isGeodesicOn side).comp_mul ell t
  change ell * t ∈ Icc (0 : ℝ) ell
  exact ⟨mul_nonneg hell.le ht.1, by nlinarith [ht.2]⟩





theorem m64MinimizingSide_normalized_speed {ell : ℝ} (hell : 0 < ell)
    {p q : M} (side : M63MinimizingGeodesicSide g D ell p q) :
    g.tangentNorm (side.map (ell * 0))
      (curveVelocity (fun t => side.map (ell * t)) 0) = (g.edist p q).toReal := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) side.map (ell * 0) := by
    rw [mul_zero]
    exact (side.smooth.contMDiffAt
      (side.domain_open.mem_nhds (side.interval_subset ⟨le_rfl, hell.le⟩))).mdifferentiableAt
        (by simp)
  have hparam : HasDerivAt (fun t : ℝ => ell * t) ell 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul ell
  rw [M63.curveVelocity_comp hd hparam, g.tangentNorm_smul, abs_of_pos hell,
    mul_zero, side.constant_speed 0 ⟨le_rfl, hell.le⟩, side.edist_eq_length hell.le,
    ENNReal.toReal_ofReal (mul_nonneg hell.le side.speed_nonnegative)]





theorem m64_exists_uniform_minimizing_side_uniqueness
    [T2Space M]
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M)) :
    ∃ r : ℝ, 0 < r ∧ ∀ {ell : ℝ}, 0 < ell → ∀ {D : LeviCivitaData g}
      {p q : M}, g.edist p q < ENNReal.ofReal r →
      ∀ side other : M63MinimizingGeodesicSide g D ell p q,
        EqOn other.map side.map (Icc (0 : ℝ) ell) := by
  classical
  choose O hOopen hOmem hOuniq using m64_exists_local_unit_geodesic_uniqueness g
  let U : Set (M × M) := ⋃ p0 : M, O p0 ×ˢ O p0
  have hUopen : IsOpen U := isOpen_iUnion fun p0 => (hOopen p0).prod (hOopen p0)
  have hUdiag (p : M) : (p, p) ∈ U := mem_iUnion.mpr ⟨p, hOmem p, hOmem p⟩
  obtain ⟨r, hr, hrU⟩ :=
    Proofs.M58.exists_uniform_riemannian_radius g hcompact hUopen hUdiag
  refine ⟨r, hr, ?_⟩
  intro ell hell D p q hpq side other
  obtain ⟨p0, hp, hq⟩ := mem_iUnion.mp (hrU p q hpq)
  have heq := hOuniq p0 p hp q hq
    (fun t => other.map (ell * t)) (fun t => side.map (ell * t))
    (m64MinimizingSide_normalized_geodesic hell other)
    (m64MinimizingSide_normalized_geodesic hell side)
    (by simpa only [mul_zero] using other.start)
    (by simpa only [mul_zero] using side.start)
    (by simpa only [mul_one] using other.finish)
    (by simpa only [mul_one] using side.finish)
    (m64MinimizingSide_normalized_speed hell other)
    (m64MinimizingSide_normalized_speed hell side)
  intro s hs
  have hunit : s / ell ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hell.le, (div_le_one hell).mpr hs.2⟩
  have hscale : ell * (s / ell) = s := by field_simp [hell.ne']
  simpa only [hscale] using heq hunit

end PoincareConjecture
