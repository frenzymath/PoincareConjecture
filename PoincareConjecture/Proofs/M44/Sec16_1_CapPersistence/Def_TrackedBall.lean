import PoincareConjecture.Definitions.Ch16.CapPersistence










set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem lt_surgeryCapEnd {t H h theta : ℝ}
    (ht : t < H) (hh : 0 < h) (htheta : 0 < theta) :
    t < surgeryCapEnd t H h theta := by
  exact lt_min ht (lt_add_of_pos_right t (mul_pos htheta (sq_pos_of_pos hh)))


theorem surgeryCapDuration_pos {t H h theta : ℝ}
    (ht : t < H) (hh : 0 < h) (htheta : 0 < theta) :
    0 < surgeryCapDuration t H h theta := by
  exact div_pos (sub_pos.mpr (lt_surgeryCapEnd ht hh htheta)) (sq_pos_of_pos hh)



theorem surgeryCapDuration_le {t H h theta : ℝ} (hh : 0 < h) :
    surgeryCapDuration t H h theta ≤ theta := by
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  have he := min_le_right H (t + theta * h ^ 2)
  dsimp [surgeryCapEnd] at *
  linarith



theorem surgeryCap_physical_time (t h s : ℝ) :
    t + s / (h⁻¹ ^ 2) = t + s * h ^ 2 := by
  simp only [inv_pow, div_inv_eq_mul]



theorem surgeryCap_physical_time_mem {t H h theta s : ℝ}
    (hh : 0 < h) (hs : s ∈ Set.Ico 0 (surgeryCapDuration t H h theta)) :
    t + s / (h⁻¹ ^ 2) ∈ Set.Ico t (surgeryCapEnd t H h theta) := by
  rw [surgeryCap_physical_time]
  have hupper := (lt_div_iff₀ (sq_pos_of_pos hh)).mp hs.2
  exact ⟨le_add_of_nonneg_right (mul_nonneg hs.1 (sq_nonneg h)), by linarith⟩



theorem surgeryCap_normalized_time_mem_iff {t H h theta x : ℝ} (hh : 0 < h) :
    (x - t) / h ^ 2 ∈ Set.Ico 0 (surgeryCapDuration t H h theta) ↔
      x ∈ Set.Ico t (surgeryCapEnd t H h theta) := by
  simp only [Set.mem_Ico, surgeryCapDuration,
    div_lt_div_iff_of_pos_right (sq_pos_of_pos hh), sub_lt_sub_iff_right]
  constructor
  · rintro ⟨hlo, hhi⟩
    have h := (le_div_iff₀ (sq_pos_of_pos hh)).mp hlo
    exact ⟨by linarith, hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨div_nonneg (sub_nonneg.mpr hlo) (sq_nonneg h), hhi⟩



theorem surgeryCap_model_time_mem {t H h theta s : ℝ}
    (hh : 0 < h) (htheta : theta < 1)
    (hs : s ∈ Set.Ico 0 (surgeryCapDuration t H h theta)) :
    s ∈ Set.Ico 0 (1 : ℝ) :=
  ⟨hs.1, (hs.2.trans_le (surgeryCapDuration_le hh)).trans htheta⟩



theorem surgeryCap_time_subset {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) {t theta : ℝ}
    (ht : t ∈ surgeryObservationInterval O) :
    (fun s => t + s / ((F.parameters.h t)⁻¹ ^ 2)) ''
      Set.Ico 0 (surgeryCapDuration t O.H (F.parameters.h t) theta) ⊆
        F.time_domain := by
  rintro _ ⟨s, hs, rfl⟩
  have htime := surgeryCap_physical_time_mem (F.parameters.h_pos t ht.1) hs
  apply O.interval_subset
  exact ⟨ht.1.trans htime.1, htime.2.trans_le (min_le_left _ _)⟩

namespace SurgeryRegularSlab

variable {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
  (S : SurgeryRegularSlab slice metric a b)



theorem identify_initial_heq (s : Set.Icc a b) (hs : s.1 = a)
    (x : (slice a).carrier) : HEq (S.identify s x) x := by
  rcases s with ⟨s, hsI⟩
  dsimp only at hs
  subst s
  exact heq_of_eq (S.initial_identify x)



theorem transport_self (s : Set.Icc a b) (x : (slice s.1).carrier) :
    S.transport s s x = x := by
  exact (S.identify s).apply_symm_apply x



theorem transport_trans (r s t : Set.Icc a b) (x : (slice r.1).carrier) :
    S.transport s t (S.transport r s x) = S.transport r t x := by
  simp only [transport, Diffeomorph.symm_apply_apply]



theorem transport_contMDiff (s t : Set.Icc a b) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (S.transport s t) :=
  (S.identify t).contMDiff.comp (S.identify s).symm.contMDiff

end SurgeryRegularSlab

end PoincareConjecture
