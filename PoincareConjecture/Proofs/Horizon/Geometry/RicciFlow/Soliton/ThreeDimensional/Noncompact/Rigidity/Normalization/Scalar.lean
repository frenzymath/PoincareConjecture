import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]

theorem hasDerivAt_scalarCurvature_round_surface
    {J : Set ℝ} (H : RicciFlow 2 N J) {t : ℝ} (ht : t ∈ interior J)
    (hround : ConstantPositiveSectionalCurvature (H.metric t) (H.connection t))
    (x : N) :
    HasDerivAt (fun s ↦ (H.connection s).scalarCurvature x)
      ((H.connection t).scalarCurvature x ^ 2) t := by
  obtain ⟨R, _, hR⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp hround
  have hconst : (H.connection t).scalarCurvature = fun _ ↦ R := funext hR
  have hlap : (H.connection t).laplacian (H.connection t).scalarCurvature x = 0 := by
    rw [hconst]
    simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const,
      zero_apply, sub_self, Finset.sum_const_zero]
  simpa only [hlap, zero_add] using H.hasDerivAt_scalarCurvature_surface ht x

theorem eq_inverse_one_sub_of_riccati_lower_bound
    {R : ℝ → ℝ} (hpositive : ∀ t < 1, 0 < R t)
    (hderivative : ∀ t < 1, HasDerivAt R (R t ^ 2) t)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ t < 1, c / (1 - t) ≤ R t) :
    ∀ t < 1, R t = 1 / (1 - t) := by
  have hinv (s : ℝ) (hs : s < 1) :
      HasDerivAt (fun t ↦ (R t)⁻¹) (-1) s := by
    have h := (hderivative s hs).inv (hpositive s hs).ne'
    convert! h using 1
    simp [(hpositive s hs).ne']
  have hsum (s : ℝ) (hs : s < 1) :
      HasDerivAt (fun t ↦ (R t)⁻¹ + t) 0 s := by
    convert! (hinv s hs).add (hasDerivAt_id s) using 1
    norm_num
  let A := (R 0)⁻¹
  have hconstant (s : ℝ) (hs : s < 1) : (R s)⁻¹ + s = A := by
    have h := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (1 : ℝ)).isPreconnected
      (fun t ht ↦ (hsum t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hsum t ht).deriv) hs (show (0 : ℝ) ∈ Iio 1 by norm_num)
    simpa only [add_zero] using h
  have hinverse (s : ℝ) (hs : s < 1) : (R s)⁻¹ = A - s := by
    linarith [hconstant s hs]
  have hAlo : 1 ≤ A := by
    by_contra h
    have hA : A < 1 := lt_of_not_ge h
    have hs : (A + 1) / 2 < 1 := by linarith
    have hp := inv_pos.mpr (hpositive ((A + 1) / 2) hs)
    rw [hinverse _ hs] at hp
    linarith
  have hbound (s : ℝ) (hs : s < 1) : c * (A - s) ≤ 1 - s := by
    have h := (div_le_iff₀ (sub_pos.mpr hs)).mp (hlower s hs)
    have h' : c / R s ≤ 1 - s :=
      (div_le_iff₀ (hpositive s hs)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, hinverse s hs] using h'
  have hlim : Tendsto (fun s : ℝ ↦ c * (A - s) - (1 - s))
      (𝓝[<] (1 : ℝ)) (𝓝 (c * (A - 1))) := by
    have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self, sub_zero] using
      ((tendsto_const_nhds (x := c)).mul ((tendsto_const_nhds (x := A)).sub hid)).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hid)
  have hprod : c * (A - 1) ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_nonpos.mpr (hbound s hs)
  have hA : A = 1 := by nlinarith
  intro t ht
  have h := hinverse t ht
  rw [hA] at h
  have hi := congrArg Inv.inv h
  simpa only [inv_inv, one_div] using hi

theorem scalarCurvature_eq_one_div_one_sub_of_round_lower_bound
    (H : RicciFlow 2 N (Iio 1))
    (hround : ∀ t < 1,
      ConstantPositiveSectionalCurvature (H.metric t) (H.connection t))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ t < 1, ∀ x : N, c / (1 - t) ≤ (H.connection t).scalarCurvature x) :
    ∀ t < 1, ∀ x : N, (H.connection t).scalarCurvature x = 1 / (1 - t) := by
  intro t ht x
  apply eq_inverse_one_sub_of_riccati_lower_bound
    (R := fun s ↦ (H.connection s).scalarCurvature x) ?_ ?_ hc
    (fun s hs ↦ hlower s hs x) t ht
  · intro s hs
    exact (div_pos hc (sub_pos.mpr hs)).trans_le (hlower s hs x)
  · intro s hs
    exact H.hasDerivAt_scalarCurvature_round_surface
      (by simpa only [interior_Iio, mem_Iio] using hs) (hround s hs) x

section Ambient

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_scalarCurvature_of_spatially_constant
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hconst : ∀ x y : M,
      (F.connection t).scalarCurvature x = (F.connection t).scalarCurvature y)
    (hnorm : ∀ x : M, (F.connection t).ricciNormSq x =
      (1 / 2 : ℝ) * (F.connection t).scalarCurvature x ^ 2)
    (x : M) :
    HasDerivAt (fun s ↦ (F.connection s).scalarCurvature x)
      ((F.connection t).scalarCurvature x ^ 2) t := by
  have hscalar : (F.connection t).scalarCurvature =
      fun _ ↦ (F.connection t).scalarCurvature x := funext fun y ↦ hconst y x
  have hlap : (F.connection t).laplacian (F.connection t).scalarCurvature x = 0 := by
    rw [hscalar]
    simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const,
      zero_apply, sub_self, Finset.sum_const_zero]
  have h := F.hasDerivAt_scalarCurvature ht x
  rw [hlap, hnorm x] at h
  convert! h using 1
  ring

theorem scalarCurvature_eq_one_div_one_sub_of_spatially_constant_lower_bound
    (F : RicciFlow n M (Iio 1))
    (hconst : ∀ t < 1, ∀ x y : M,
      (F.connection t).scalarCurvature x = (F.connection t).scalarCurvature y)
    (hnorm : ∀ t < 1, ∀ x : M, (F.connection t).ricciNormSq x =
      (1 / 2 : ℝ) * (F.connection t).scalarCurvature x ^ 2)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ t < 1, ∀ x : M, c / (1 - t) ≤ (F.connection t).scalarCurvature x) :
    ∀ t < 1, ∀ x : M, (F.connection t).scalarCurvature x = 1 / (1 - t) := by
  intro t ht x
  apply eq_inverse_one_sub_of_riccati_lower_bound
    (R := fun s ↦ (F.connection s).scalarCurvature x) ?_ ?_ hc
    (fun s hs ↦ hlower s hs x) t ht
  · intro s hs
    exact (div_pos hc (sub_pos.mpr hs)).trans_le (hlower s hs x)
  · intro s hs
    exact F.hasDerivAt_scalarCurvature_of_spatially_constant
      (by simpa only [interior_Iio, mem_Iio] using hs) (hconst s hs) (hnorm s hs) x

end Ambient

end PoincareConjecture.RicciFlow
