import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckAxialLength
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicSplicing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

def neckLevelShorteningEpsilon : ℝ :=
  1 / (384 * standardSpherePathCeiling + 1)

theorem neckLevelShorteningEpsilon_pos : 0 < neckLevelShorteningEpsilon := by
  have hL := standardSpherePathCeiling_pos
  unfold neckLevelShorteningEpsilon
  positivity

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem mem_coordinate_sphere_iff (N : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (x : M) :
    x ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) ↔
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = s := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzs : z.2 = s := hz.2
    have hzA : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hzs.symm ▸ hs
    exact ⟨N.coordinate_map_mem_of_axial z hzA, by
      rw [N.coordinate_inverse_coordinate_map_of_axial z hzA]
      exact hzs⟩
  · rintro ⟨hx, hheight⟩
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hheight⟩,
      N.coordinate_map_coordinate_inverse hx⟩

theorem exists_coordinate_sphere_shortcut (N : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) {x y : M}
    (hx : x ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)))
    (hy : y ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))) :
    ∃ σ : ℝ → M, σ 0 = x ∧ σ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ ∧
      MapsTo σ univ (N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))) ∧
      g.pathELength σ 0 1 <
        ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) ∧
      σ =ᶠ[𝓝 (0 : ℝ)] (fun _ => x) ∧ σ =ᶠ[𝓝 (1 : ℝ)] (fun _ => y) := by
  obtain ⟨⟨p, a⟩, ⟨_, ha⟩, hpx⟩ := hx
  obtain ⟨⟨q, b⟩, ⟨_, hb⟩, hqy⟩ := hy
  have has : a = s := ha
  have hbs : b = s := hb
  subst a
  subst b
  obtain ⟨γ, hγ0, hγ1, hγ, hγlen, hγnear0, hγnear1⟩ :=
    exists_standardSphere_short_path p q
  let σ : ℝ → M := fun t => N.coordinate_map (γ t, s)
  have hσ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ := by
    rw [← contMDiffOn_univ]
    apply (N.coordinate_map_smooth.of_le (by simp)).comp
    · exact (hγ.prodMk contMDiff_const).contMDiffOn
    · intro t _
      exact ⟨mem_univ _, hs⟩
  refine ⟨σ, by simpa only [σ, hγ0] using hpx,
    by simpa only [σ, hγ1] using hqy, hσ, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact ⟨(γ t, s), ⟨mem_univ _, rfl⟩, rfl⟩
  · have hscale : 0 < 4 * N.scale := mul_pos (by norm_num) N.scale_pos
    have hbound := (coordinate_sphere_pathELength_le N hγ hs 0 1).trans_lt
      (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
        ENNReal.ofReal_ne_top hγlen)
    convert hbound using 1
    rw [← ENNReal.ofReal_mul hscale.le]
    congr 1
    ring
  · filter_upwards [hγnear0] with t ht
    change N.coordinate_map (γ t, s) = x
    rw [ht]
    exact hpx
  · filter_upwards [hγnear1] with t ht
    change N.coordinate_map (γ t, s) = y
    rw [ht]
    exact hqy

theorem exists_neck_level_excursion_replacement (N : EpsilonNeck g)
    (hε : N.epsilon ≤ neckLevelShorteningEpsilon) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) {U : Set M}
    (hsphere : N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) ⊆ U)
    {γ : ℝ → M} {a b c t d : ℝ}
    (hac : a ≤ c) (hct : c ≤ t) (htd : t ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hc : γ c ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)))
    (hd : γ d ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)))
    (hγN : MapsTo γ (Icc c t) N.carrier)
    (hheight : N.epsilon⁻¹ / 24 ≤
      |(N.coordinate_inverse (γ t)).2 - (N.coordinate_inverse (γ c)).2|) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 96) ≤
        g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hrecip : 384 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hε
    simpa only [neckLevelShorteningEpsilon, one_div_one_div, one_div, inv_inv] using h
  have hdelta : 0 < N.scale * N.epsilon⁻¹ / 96 :=
    div_pos (mul_pos N.scale_pos (inv_pos.mpr N.epsilon_pos)) (by norm_num)
  have hbudget : (4 * standardSpherePathCeiling) * N.scale +
      N.scale * N.epsilon⁻¹ / 96 ≤ (N.scale / 2) * (N.epsilon⁻¹ / 24) := by
    have h := mul_le_mul_of_nonneg_right hrecip N.scale_pos.le
    nlinarith [N.scale_pos]
  have hcost : ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 24)) ≤
      g.pathELength γ c d := by
    calc
      _ ≤ ENNReal.ofReal ((N.scale / 2) *
          |(N.coordinate_inverse (γ t)).2 - (N.coordinate_inverse (γ c)).2|) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hheight
          (div_nonneg N.scale_pos.le (by norm_num)))
      _ ≤ g.pathELength γ c t := path_axial_displacement_le N hct
        (hγ.mono (Icc_subset_Icc hac (htd.trans hdb))) hγN
      _ ≤ g.pathELength γ c d := Manifold.pathELength_mono le_rfl htd
  obtain ⟨α, hα0, hα1, hα, hαS, hαlen, _, _⟩ :=
    exists_coordinate_sphere_shortcut N hs hc hd
  have hsave : g.pathELength α 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 96) ≤
      g.pathELength γ c d := by
    calc
      _ ≤ ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) +
          ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 96) := add_le_add hαlen.le le_rfl
      _ = ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale +
          N.scale * N.epsilon⁻¹ / 96) :=
        (ENNReal.ofReal_add
          (mul_nonneg (mul_nonneg (by norm_num) standardSpherePathCeiling_pos.le)
            N.scale_pos.le) hdelta.le).symm
      _ ≤ ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 24)) :=
        ENNReal.ofReal_le_ofReal hbudget
      _ ≤ g.pathELength γ c d := hcost
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσlen⟩ :=
    exists_intrinsic_subarc_replacement g hac (hct.trans htd) hdb hγ hγU
      hα.contMDiffOn (fun t _ => hsphere (hαS (mem_univ t))) hα0 hα1
  refine ⟨σ, hσ0, hσ1, hσ, hσU, ?_⟩
  calc
    _ = g.pathELength γ a c +
        (g.pathELength α 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 96)) +
        g.pathELength γ d b := by rw [hσlen]; ac_rfl
    _ ≤ g.pathELength γ a c + g.pathELength γ c d + g.pathELength γ d b :=
      add_le_add (add_le_add le_rfl hsave) le_rfl
    _ = g.pathELength γ a b := by
      change Manifold.pathELength (𝓡 3) γ a c +
        Manifold.pathELength (𝓡 3) γ c d + Manifold.pathELength (𝓡 3) γ d b =
          Manifold.pathELength (𝓡 3) γ a b
      rw [Manifold.pathELength_add hac (hct.trans htd),
        Manifold.pathELength_add (hac.trans (hct.trans htd)) hdb]

end PoincareConjecture.M28
