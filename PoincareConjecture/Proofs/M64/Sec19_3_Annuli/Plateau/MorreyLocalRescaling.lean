import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyHolderRepresentative
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakRescaling













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Pointwise ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak M60

local notation "Plane" => EuclideanSpace ℝ (Fin 2)




theorem m64Morrey_affine_image_ball (a b : Plane) {rho : ℝ} (hrho : 0 < rho)
    (r : ℝ) :
    (fun z : Plane => a + rho • z) '' ball b r = ball (a + rho • b) (rho * r) := by
  change ((fun z : Plane => a + z) ∘ (fun z => rho • z)) '' ball b r = _
  rw [image_comp]
  change (fun z : Plane => a + z) '' (rho • ball b r) = _
  rw [_root_.smul_ball hrho.ne', Real.norm_of_nonneg hrho.le]
  exact (IsometryEquiv.addLeft a).image_ball (rho • b) (rho * r)




theorem m64Morrey_local_disk_holder_representative {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {rho K beta : ℝ}
    (hrho : 0 < rho)
    (hu : MemLp u 2 (volume.restrict (ball a (rho * 2))))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a (rho * 2))))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => V i y b) (fun y => u y b)
      (ball a (rho * 2))) (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ i : Fin 2, ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ y in ball b r, ‖V i y‖ ^ 2) ≤ K * r ^ beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U : Plane → EuclideanSpace ℝ (Fin m),
      ContinuousOn U (closedBall a (rho / 2)) ∧
      U =ᵐ[volume.restrict (ball a (rho / 2))] u ∧
      ∀ x ∈ closedBall a (rho / 2), ∀ y ∈ closedBall a (rho / 2),
        dist (U x) (U y) ≤ C * (dist x y) ^ (beta / 2) := by
  let e := suAffineHomeomorph a hrho
  let v : Plane → EuclideanSpace ℝ (Fin m) := fun z => u (a + rho • z)
  let p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) :=
    fun i z => rho • V i (a + rho • z)
  have hv : MemLp v 2 (volume.restrict (ball (0 : Plane) 2)) := by
    simpa only [suAffine_preimage_ball a hrho] using suAffine_memLp hu a hrho
  have hp (i : Fin 2) : MemLp (p i) 2 (volume.restrict (ball (0 : Plane) 2)) := by
    simpa +instances only [suAffine_preimage_ball a hrho, p, Pi.smul_apply] using!
      (suAffine_memLp (hV i) a hrho).const_smul rho
  have hweak (i : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv i (fun z => p i z b) (fun z => v z b) (ball (0 : Plane) 2) := by
    simpa only [suAffine_preimage_ball a hrho, p, v, PiLp.smul_apply, smul_eq_mul] using
      suAffine_weakPartial (hw i b) a hrho
  have hgrowth (i : Fin 2) (b : Plane) (hb : b ∈ closedBall (0 : Plane) 1)
      (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
      (∫ z in ball b r, ‖p i z‖ ^ 2) ≤ (K * rho ^ beta) * r ^ beta := by
    have hb' : a + rho • b ∈ closedBall a rho := by
      have hh : a + rho • b ∈ (fun z : Plane => a + rho • z) '' closedBall 0 1 :=
        ⟨b, hb, rfl⟩
      simpa only [suRescale_closedBall a hrho, mul_one] using hh
    have hr' : rho * r ∈ Ioc (0 : ℝ) rho :=
      ⟨mul_pos hrho hr.1, (mul_le_mul_of_nonneg_left hr.2 hrho.le).trans_eq (mul_one rho)⟩
    calc
      (∫ z in ball b r, ‖p i z‖ ^ 2) =
          ∫ z in ball b r, rho ^ 2 * ‖V i (a + rho • z)‖ ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [p, norm_smul, Real.norm_of_nonneg hrho.le, mul_pow]
      _ = ∫ y in ball (a + rho • b) (rho * r), ‖V i y‖ ^ 2 := by
        simpa +instances only [m64Morrey_affine_image_ball a b hrho] using!
          suRescale_integral (fun y : Plane => ‖V i y‖ ^ 2) a hrho (ball b r)
      _ ≤ K * (rho * r) ^ beta := henergy i _ hb' _ hr'
      _ = (K * rho ^ beta) * r ^ beta := by
        rw [Real.mul_rpow hrho.le hr.1.le, mul_assoc]
  obtain ⟨C, hC, W, hW, hWae, hholder⟩ := m64Morrey_holder_representative
    hv hp hweak (mul_nonneg hK (Real.rpow_nonneg hrho.le _)) hbeta hgrowth
  let U := W ∘ e.symm
  have himage : e '' closedBall (0 : Plane) (1 / 2) = closedBall a (rho / 2) := by
    change (fun z : Plane => a + rho • z) '' closedBall 0 (1 / 2) = _
    simpa only [mul_one_div] using suRescale_closedBall a hrho (1 / 2)
  have hmaps : MapsTo e.symm (closedBall a (rho / 2)) (closedBall (0 : Plane) (1 / 2)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hx
    simpa using hz
  have haeU : U =ᵐ[volume.restrict (ball a (rho / 2))] u := by
    have hmap := suAffine_map_restrict a hrho (ball a (rho * (1 / 2)))
    rw [suAffine_preimage_ball a hrho, mul_one_div] at hmap
    have hae : U =ᵐ[(volume.restrict (ball (0 : Plane) (1 / 2))).map e] u := by
      rw [Filter.EventuallyEq, e.measurableEmbedding.ae_map_iff]
      filter_upwards [hWae] with z hz
      change W (e.symm (e z)) = u (e z)
      rw [e.symm_apply_apply]
      change W z = u (a + rho • z)
      exact hz
    change U =ᵐ[(volume.restrict (ball (0 : Plane) (1 / 2))).map
      (fun z : Plane => a + rho • z)] u at hae
    rw [hmap] at hae
    exact (Measure.ae_ennreal_smul_measure_iff
      (by positivity : ENNReal.ofReal ((rho ^ 2)⁻¹) ≠ 0)).mp hae
  refine ⟨C / rho ^ (beta / 2), div_nonneg hC (Real.rpow_nonneg hrho.le _), U,
    hW.comp e.symm.continuous.continuousOn hmaps, haeU, ?_⟩
  intro x hx y hy
  have hdist : dist (e.symm x) (e.symm y) = dist x y / rho := by
    apply (eq_div_iff hrho.ne').mpr
    calc
      _ = dist (e (e.symm x)) (e (e.symm y)) := by
        change dist (e.symm x) (e.symm y) * rho =
          dist (a + rho • e.symm x) (a + rho • e.symm y)
        rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hrho.le, mul_comm]
      _ = _ := by rw [e.apply_symm_apply, e.apply_symm_apply]
  calc
    _ ≤ C * (dist (e.symm x) (e.symm y)) ^ (beta / 2) :=
      hholder _ (hmaps hx) _ (hmaps hy)
    _ = _ := by
      rw [hdist, Real.div_rpow dist_nonneg hrho.le]
      ring



theorem m64Morrey_local_disk_representative {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {rho K beta : ℝ}
    (hrho : 0 < rho)
    (hu : MemLp u 2 (volume.restrict (ball a (rho * 2))))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a (rho * 2))))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => V i y b) (fun y => u y b)
      (ball a (rho * 2))) (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ i : Fin 2, ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ y in ball b r, ‖V i y‖ ^ 2) ≤ K * r ^ beta) :
    ∃ U : Plane → EuclideanSpace ℝ (Fin m),
      ContinuousOn U (closedBall a (rho / 2)) ∧
      U =ᵐ[volume.restrict (ball a (rho / 2))] u := by
  obtain ⟨_, _, U, hU, hUae, -⟩ := m64Morrey_local_disk_holder_representative
    hrho hu hV hw hK hbeta henergy
  exact ⟨U, hU, hUae⟩

end PoincareConjecture
