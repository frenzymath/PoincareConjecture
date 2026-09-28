import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBarrier
import PoincareConjecture.Proofs.M34.Mathlib.FirstExitOpen










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)





theorem boundary_neck_region_subset_recutCarrier
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hdelta : N.epsilon < epsilon)
    (hsmall : N.epsilon ≤ 1 / 8)
    (hscale : N.boundary_neck.scale ≤ (9 / 8 : ℝ) * N.end_neck.scale) :
    N.boundary_neck.region (-epsilon⁻¹) epsilon⁻¹ ⊆
      N.recutCarrier (2 / epsilon - N.epsilon⁻¹) := by
  let c : ℝ := -N.epsilon⁻¹ + epsilon⁻¹ / 16
  let d : ℝ := -N.epsilon⁻¹ + epsilon⁻¹ / 8
  let b : ℝ := 2 / epsilon - N.epsilon⁻¹
  have hi : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hinv : epsilon⁻¹ < N.epsilon⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt N.epsilon_pos hdelta
  have hc : -N.epsilon⁻¹ < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  have hdb : d < b := by dsimp [d, b]; simp only [div_eq_mul_inv]; linarith
  have hb : b < N.epsilon⁻¹ := by dsimp [b]; rw [div_eq_mul_inv]; linarith
  have hgap : b - d = (15 / 8 : ℝ) * epsilon⁻¹ := by dsimp [b, d]; ring
  have heB : N.boundary_neck.epsilon ≤ 1 / 8 := by rwa [N.boundary_neck_epsilon]
  have heE : N.end_neck.epsilon ≤ 1 / 8 := by rwa [N.end_neck_epsilon]
  intro x hx
  let q := (N.boundary_neck.coordinate_inverse x).1
  let z := (N.boundary_neck.coordinate_inverse x).2
  let γ : ℝ → M := fun t => N.boundary_neck.coordinate_map (q, t * z)
  have hz : z ∈ Ioo (-N.boundary_neck.epsilon⁻¹) N.boundary_neck.epsilon⁻¹ :=
    (N.boundary_neck.coordinate_inverse_mem x hx.1).2
  have hzsmall : |z| < epsilon⁻¹ := abs_lt.mpr hx.2
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) :=
    (N.boundary_neck.axialPath_contMDiffOn q hz).of_le (by simp)
  have hγmem : MapsTo γ (Icc (0 : ℝ) 1) N.carrier := by
    intro t ht
    exact N.boundary_neck_subset (N.boundary_neck.coordinate_map_mem_of_axial_mem
      (N.boundary_neck.axialPath_height_mem hz ht))
  have hγ0 : γ 0 ∈ N.closed_core := by
    apply N.boundary_subset_closed_core
    rw [N.boundary_eq_neck_sphere, N.boundary_neck.central_sphere_eq]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, by simp [γ]⟩
  have hγ1 : γ 1 = x := by
    simpa only [γ, one_mul] using N.boundary_neck.coordinate_map_coordinate_inverse hx.1
  by_contra hout
  obtain ⟨t, ht, hfront, _⟩ := hγ.continuousOn.exists_first_exit_open zero_le_one
    (N.recutCarrier_isOpen (hc.trans (hcd.trans hdb)) hb)
    (Or.inl hγ0) (hγ1.symm ▸ hout)
  have hA : 0 < (5 / 4 : ℝ) / N.end_neck.scale :=
    div_pos (by norm_num) N.end_neck.scale_pos
  have hbarrier := N.collar_height_le_pathELength_of_axial_speed hA.le
    (fun _ hy v => N.end_neck.coordinate_inverse_axial_le_tangentNorm_sharp heE hy v)
    hc hcd hdb hb ht.1.le (hγ.mono (Icc_subset_Icc_right ht.2))
    (hγmem.mono_left (Icc_subset_Icc_right ht.2)) hγ0 hfront
  have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.pathELength_mono le_rfl ht.2
  have hlength : g.pathELength γ 0 1 ≤
      ENNReal.ofReal ((5 / 4 : ℝ) * N.boundary_neck.scale * |z|) :=
    N.boundary_neck.axialPath_pathELength_le_sharp heB q hz
  have hreal : ((5 / 4 : ℝ) / N.end_neck.scale) *
      ((5 / 4 : ℝ) * N.boundary_neck.scale * |z|) < b - d := by
    have hnorm := mul_le_mul_of_nonneg_right hscale (abs_nonneg z)
    have hmul := mul_le_mul_of_nonneg_left hnorm
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 16) N.end_neck.scale_pos.le)
    have hcancel : ((25 / 16 : ℝ) / N.end_neck.scale) *
        ((9 / 8 : ℝ) * N.end_neck.scale * |z|) = (225 / 128 : ℝ) * |z| := by
      field_simp [N.end_neck.scale_pos.ne']
      ring
    rw [hcancel] at hmul
    rw [hgap]
    have heq : ((5 / 4 : ℝ) / N.end_neck.scale) *
        ((5 / 4 : ℝ) * N.boundary_neck.scale * |z|) =
        ((25 / 16 : ℝ) / N.end_neck.scale) * (N.boundary_neck.scale * |z|) := by ring
    rw [heq]
    nlinarith
  have hstrict : ENNReal.ofReal ((5 / 4 : ℝ) / N.end_neck.scale) *
      ENNReal.ofReal ((5 / 4 : ℝ) * N.boundary_neck.scale * |z|) <
        ENNReal.ofReal (b - d) := by
    rw [← ENNReal.ofReal_mul hA.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hdb)).mpr hreal
  have hweak := hbarrier.trans (mul_le_mul' le_rfl (hmono.trans hlength))
  exact not_lt_of_ge hweak hstrict

end PoincareConjecture.CapCertificate
