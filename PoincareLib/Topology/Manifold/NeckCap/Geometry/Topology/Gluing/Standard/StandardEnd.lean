import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Standard.StandardEndOuterChart
import PoincareLib.Topology.Manifold.NeckCap.Geometry.AnalyticTools.Compatible.CompatibleDiffeomorph

/-!
# A standard radial end from supplied topology data

The compatible buffered charts glue to an actual global diffeomorphism.
Restricting their radial coordinate retains both smooth directions and the
same orthogonal sphere map on any later upper tail. This is the conditional
StandardEnd assembly for Morgan--Tian A.21, pp. 510-514; see
`tasks/M25/gluing-collar/standard-end-assembly-plan.md`. The collar embedding,
Schoenflies data and sphere-isotopy data remain explicit inputs.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D.SchoenfliesData

/-- The compatible interior and exterior charts give a global smooth
Euclidean model with the prescribed radial formula on a retained upper
tail. Both topology data remain inputs. StandardEnd assembly, sections
2-5, for MT A.21, pp. 510-514. -/
theorem exists_standardEnd_of_data
    {W : Type u} [TopologicalSpace W] [ChartedSpace E3 W]
    [IsManifold (𝓡 3) ∞ W]
    (Phi0 : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W)
    {a b c h δ tl tm tu v : ℝ}
    (S : SchoenfliesData (fun p => Phi0 (e (p.1, c + h * p.2))) δ)
    (D : DiffSphereIsotopyData S.boundary_map)
    (hsource : e.source = univ ×ˢ Ioo a b)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hEmbedding : IsCollarEmbedding (fun p => Phi0 (e (p.1, c + h * p.2))))
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b)
    (hδ : 0 ≤ δ) (hlo : δ < tl) (hlm : tl < tm) (hmu : tm < tu) (hhi : tu < 1)
    (hv : v ∈ Ico (c + h * tu) b) :
    ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
      (r0 : ℝ) (sigma : OpenPartialHomeomorph ℝ ℝ),
      0 < r0 ∧ sigma.source = Ioo v b ∧ sigma.target = Ioi r0 ∧
      ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
      ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
      StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
      (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) ∧
      (∀ q : UnitTwoSphere, ∀ s ∈ Ioo v b,
        Phi (e (q, s)) = sigma s • (sphereMap D.isometry q).1) := by
  let l := c + h * tl
  let m := c + h * tm
  let u := c + h * tu
  have hLl : c + h * δ < l := by
    dsimp only [l]
    linarith [mul_lt_mul_of_pos_left hlo hh]
  have hlm' : l < m := by
    dsimp only [l, m]
    linarith [mul_lt_mul_of_pos_left hlm hh]
  have hmu' : m < u := by
    dsimp only [m, u]
    linarith [mul_lt_mul_of_pos_left hmu hh]
  have hlv : l < v := (hlm'.trans hmu').trans_le hv.1
  obtain ⟨rho, I, O, hRsource, hRtarget, hRf, hRi, hReq, hRmono, hRpos, hRder,
    _, _, _, _, hOsource, _, hIf, hOf, hIi, hOi, hcover, htarget,
    hforward, hinverse, _, hOtail⟩ :=
    S.exists_compatible_buffered_end_charts Phi0 e D hsource he hei hend hEmbedding
      hh ha hb hδ hlo hlm hmu hhi
  obtain ⟨Phi, _, hPhiO, _, _⟩ :=
    OpenPartialHomeomorph.m25_exists_diffeomorph_of_compatible I O hcover htarget
      hIf hOf hIi hOi hforward hinverse
  have hRanchor : rho l = S.radial tl := by
    have hnormalize : (l - c) / h = tl := by
      dsimp only [l]
      field_simp [hh.ne']
      ring
    exact (hReq ⟨le_rfl, hlm'.le⟩).trans (congrArg S.radial hnormalize)
  have hRtarget' : rho.target = Ioi (rho l) := by
    rw [hRanchor]
    exact hRtarget
  have hRf' : ContDiffOn ℝ ∞ (rho : ℝ → ℝ) rho.source := by
    apply hRf.mono
    rw [hRsource]
    exact fun _ hs => ⟨hLl.trans hs.1, hs.2⟩
  have hRder' : ∀ s ∈ rho.source, 0 < deriv (rho : ℝ → ℝ) s := by
    intro s hs
    rw [hRsource] at hs
    exact hRder s ⟨hs.1.le, hs.2⟩
  obtain ⟨sigma, hSsource, hStarget, hSforward, _, hr0, hSf, hSi, hSmono, hSder⟩ :=
    rho.exists_smooth_radial_restriction hRsource hRtarget' hRf' hRi hRmono
      hRpos hRder' ⟨hlv.le, hv.2⟩
  refine ⟨Phi, rho v, sigma, hr0, hSsource, hStarget, hSf, hSi, hSmono, hSder, ?_⟩
  intro q s hs
  have hOs : e (q, s) ∈ O.source := by
    rw [hOsource]
    exact ⟨(q, s), ⟨mem_univ _, hlv.trans hs.1, hs.2⟩, rfl⟩
  calc
    Phi (e (q, s)) = O (e (q, s)) := hPhiO hOs
    _ = rho s • (sphereMap D.isometry q).1 := hOtail q s ⟨hv.1.trans hs.1.le, hs.2⟩
    _ = sigma s • (sphereMap D.isometry q).1 := by rw [hSforward]

end PoincareMT.M25.Topology3D.SchoenfliesData
