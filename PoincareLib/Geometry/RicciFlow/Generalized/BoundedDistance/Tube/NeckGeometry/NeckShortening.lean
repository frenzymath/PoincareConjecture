import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicSplicing
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckSpherePaths
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckAxialLength

/-!
# Actual endpoint-neck shortening

Morgan--Tian Lemma A.1, pp. 497-498, as used in Claim 10.3, pp. 248-249.
The actual central-sphere path replaces an excursion containing a literal
half-neck subarc. The fixed saving `scale / (8 * epsilon)` is weaker than
the printed A.1 constant and sufficient for compact confinement. See
`proof-work/tasks/M28/review-endpoints/2026-09-23-endpoint-neck-shortening.md`.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareMT.M28

/-- One shortening threshold, chosen from the fixed sphere before any
ambient manifold, neck, region or path is supplied. -/
def neckShorteningEpsilon : ℝ := 1 / (32 * standardSpherePathCeiling + 1)

/-- The universal shortening threshold is positive. -/
theorem neckShorteningEpsilon_pos : 0 < neckShorteningEpsilon := by
  have hL := standardSpherePathCeiling_pos
  unfold neckShorteningEpsilon
  positivity

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- Every fixed actual neck supplies a positive saving, independent of
the index of any later sequence of competitors. -/
theorem neck_shortening_saving_pos (N : EpsilonNeck g) :
    0 < N.scale * N.epsilon⁻¹ / 8 := by
  exact div_pos (mul_pos N.scale_pos (inv_pos.mpr N.epsilon_pos)) (by norm_num)

/-- A literal half-neck subarc pays for an actual central-sphere shortcut
and a fixed positive saving. The input is geometric containment and axial
displacement, not a proposed length bound (Lemma A.1). -/
theorem exists_neck_excursion_shortcut (N : EpsilonNeck g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {γ : ℝ → M} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (ha : γ a ∈ N.central_sphere) (hb : γ b ∈ N.central_sphere)
    (hγN : MapsTo γ (Icc c d) N.carrier)
    (hheight : N.epsilon⁻¹ / 2 ≤
      |(N.coordinate_inverse (γ d)).2 - (N.coordinate_inverse (γ c)).2|) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ ∧ MapsTo σ univ N.central_sphere ∧
      g.pathELength σ 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) ≤
        g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hrecip : 32 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hepsilon
    simpa only [neckShorteningEpsilon, one_div_one_div, one_div, inv_inv] using h
  have hbudget : (4 * standardSpherePathCeiling) * N.scale +
      N.scale * N.epsilon⁻¹ / 8 ≤ (N.scale / 2) * (N.epsilon⁻¹ / 2) := by
    have h := mul_le_mul_of_nonneg_right hrecip N.scale_pos.le
    nlinarith [N.scale_pos]
  have hcost : ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 2)) ≤
      g.pathELength γ a b := by
    calc
      _ ≤ ENNReal.ofReal ((N.scale / 2) *
          |(N.coordinate_inverse (γ d)).2 - (N.coordinate_inverse (γ c)).2|) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hheight
            (div_nonneg N.scale_pos.le (by norm_num)))
      _ ≤ g.pathELength γ c d := path_axial_displacement_le N hcd
        (hγ.mono (Icc_subset_Icc hac hdb)) hγN
      _ ≤ g.pathELength γ a b := Manifold.pathELength_mono hac hdb
  obtain ⟨σ, h0, h1, hσ, hσN, hlength, _, _⟩ :=
    exists_central_sphere_shortcut N ha hb
  refine ⟨σ, h0, h1, hσ, hσN, ?_⟩
  calc
    _ ≤ ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) +
        ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) :=
      add_le_add hlength.le le_rfl
    _ = ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale +
        N.scale * N.epsilon⁻¹ / 8) :=
      (ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg (by norm_num) standardSpherePathCeiling_pos.le)
          N.scale_pos.le) (neck_shortening_saving_pos N).le).symm
    _ ≤ ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 2)) :=
      ENNReal.ofReal_le_ofReal hbudget
    _ ≤ g.pathELength γ a b := hcost

/-- Replacing an actual neck excursion produces a full admissible C1
competitor in the same region, with the derived positive saving. Both
replacement endpoints are on the literal central sphere (Lemma A.1). -/
theorem exists_neck_excursion_replacement (N : EpsilonNeck g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {U : Set M} (hNU : N.central_sphere ⊆ U)
    {γ : ℝ → M} {a b c d v w : ℝ}
    (hac : a ≤ c) (hcv : c ≤ v) (hvw : v ≤ w)
    (hwd : w ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hc : γ c ∈ N.central_sphere) (hd : γ d ∈ N.central_sphere)
    (hγN : MapsTo γ (Icc v w) N.carrier)
    (hheight : N.epsilon⁻¹ / 2 ≤
      |(N.coordinate_inverse (γ w)).2 - (N.coordinate_inverse (γ v)).2|) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) ≤
        g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcd : c ≤ d := hcv.trans (hvw.trans hwd)
  obtain ⟨α, hα0, hα1, hα, hαN, hsave⟩ :=
    exists_neck_excursion_shortcut N hepsilon hcv hvw hwd
      (hγ.mono (Icc_subset_Icc hac hdb)) hc hd hγN hheight
  have hαU : MapsTo α (Icc (0 : ℝ) 1) U :=
    fun t _ => hNU (hαN (mem_univ t))
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσlen⟩ :=
    exists_intrinsic_subarc_replacement g hac hcd hdb hγ hγU
      hα.contMDiffOn hαU hα0 hα1
  refine ⟨σ, hσ0, hσ1, hσ, hσU, ?_⟩
  calc
    _ = g.pathELength γ a c +
        (g.pathELength α 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8)) +
        g.pathELength γ d b := by rw [hσlen]; ac_rfl
    _ ≤ g.pathELength γ a c + g.pathELength γ c d + g.pathELength γ d b :=
      add_le_add (add_le_add le_rfl hsave) le_rfl
    _ = g.pathELength γ a b := by
      change Manifold.pathELength (𝓡 3) γ a c +
        Manifold.pathELength (𝓡 3) γ c d +
        Manifold.pathELength (𝓡 3) γ d b = Manifold.pathELength (𝓡 3) γ a b
      rw [Manifold.pathELength_add hac hcd,
        Manifold.pathELength_add (hac.trans hcd) hdb]

end PoincareMT.M28
