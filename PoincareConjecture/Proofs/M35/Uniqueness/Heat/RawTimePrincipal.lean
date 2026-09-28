import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawEllipticity
import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatEnergy
import PoincareConjecture.Proofs.M03.ConnectionFamily
import Mathlib.Topology.UniformSpace.HeineCantor










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem rawCoordinateGram_family_continuousOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContinuousOn (fun p : ℝ × V => rawCoordinateGram (F.metric p.1) p.2)
      (J ×ˢ univ) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hi := euclidean_field_contMDiff
    (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)) :
      ContDiff ℝ ∞ (fun _ : V => EuclideanSpace.single i (1 : ℝ)))
  have hj := euclidean_field_contMDiff
    (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)) :
      ContDiff ℝ ∞ (fun _ : V => EuclideanSpace.single j (1 : ℝ)))
  exact (Proofs.M03.contMDiffOn_family_metric_pair F.smooth _ _
    hi.contMDiffOn hj.contMDiffOn).continuousOn

theorem rawInverseGram_family_continuousOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContinuousOn (fun p : ℝ × V => (rawCoordinateGram (F.metric p.1) p.2)⁻¹)
      (J ×ˢ univ) :=
  DeTurckNative.continuousOn_inverse_posDef _ (rawCoordinateGram_family_continuousOn F)
    (fun p _ => rawCoordinateGram_posDef (F.metric p.1) p.2)



theorem exists_raw_slab_ellipticity {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {K : Set V} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ I, ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      c * ‖ξ‖ ^ 2 ≤ DeTurckNative.quadratic (rawCoordinateGram (F.metric t) x)⁻¹ ξ := by
  obtain ⟨c, hc, hb⟩ := DeTurckNative.exists_uniform_inverse_quadratic_lower_bound
    (fun p : ℝ × V => rawCoordinateGram (F.metric p.1) p.2) (hI.prod hK)
    ((rawCoordinateGram_family_continuousOn F).mono (prod_mono hIJ (subset_univ K)))
    (fun p _ => rawCoordinateGram_posDef (F.metric p.1) p.2)
  exact ⟨c, hc, fun t ht x hx ξ => hb (t, x) ⟨ht, hx⟩ ξ⟩



theorem exists_raw_principal_small_time_change {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ a + τ < b ∧ ∀ t ∈ Icc a (a + τ), ∀ x ∈ K,
      ‖(rawCoordinateGram (F.metric t) x)⁻¹ -
        (rawCoordinateGram (F.metric a) x)⁻¹‖ < ε := by
  have hc := (rawInverseGram_family_continuousOn F).mono
    (prod_mono hJ (subset_univ K))
  have hu := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc
  obtain ⟨δ, hδ, hbδ⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let τ := min ((b - a) / 2) (δ / 2)
  have hτ : 0 < τ := lt_min (by linarith) (by linarith)
  have hτb : a + τ < b := by
    have h := min_le_left ((b - a) / 2) (δ / 2)
    dsimp only [τ]
    linarith
  refine ⟨τ, hτ, hτb, ?_⟩
  intro t ht x hx
  have htI : t ∈ Icc a b := ⟨ht.1, ht.2.trans hτb.le⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hd : dist (t, x) (a, x) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have h := min_le_right ((b - a) / 2) (δ / 2)
    change min ((b - a) / 2) (δ / 2) ≤ δ / 2 at h
    dsimp only [τ] at ht
    linarith only [h, hδ, ht.2]
  simpa only [dist_eq_norm] using hbδ (t, x) ⟨htI, hx⟩ (a, x) ⟨haI, hx⟩ hd

end PoincareConjecture.M35.Uniqueness.Heat
