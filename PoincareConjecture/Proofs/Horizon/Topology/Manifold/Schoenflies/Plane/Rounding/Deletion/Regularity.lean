import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Local

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_roundedVertexPath_eq_local {ρ : ℝ → ℝ} (P : ℤ → E) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (hρ : Differentiable ℝ ρ)
    (i : ℤ) {t : ℝ} (ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ)) :
    deriv (roundedVertexPath ρ P) t =
      deriv (roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i)) (t - i) := by
  have hΓ := hasDerivAt_roundedCorner (P i) (P i - P (i - 1))
    (P (i + 1) - P i) (hρ (t - i))
  have hd := (hΓ.congr_deriv hΓ.deriv.symm).scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  simp only [Function.comp_def, one_smul, id_eq] at hd
  apply (hd.congr_of_eventuallyEq ?_).deriv
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact roundedVertexPath_eq_local P hδ hδhalf htail hbound i hs

theorem roundedCorner_comp_projection_deriv_pos {ρ h : ℝ → ℝ} (p u v : E)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1)
    (ℓ : E →L[ℝ] ℝ) (hu : 0 < ℓ u) (hv : 0 < ℓ v) {t : ℝ}
    (hh : DifferentiableAt ℝ h t) (hpos : 0 < deriv h t) :
    0 < ℓ (deriv (fun s => roundedCorner ρ p u v (h s)) t) := by
  have hΓ := hasDerivAt_roundedCorner p u v (hρ (h t))
  have hd := (hΓ.congr_deriv hΓ.deriv.symm).scomp t hh.hasDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.deriv, map_smul, smul_eq_mul]
  exact mul_pos hpos ((strictMono_roundedCorner_projection p u v hρ hder ℓ hu hv).1 (h t))

theorem IsSimplePolygon.exists_positive_integer_corner_functional
    [FiniteDimensional ℝ E] {N : ℕ} [NeZero N] {p : Polygon E N}
    (hp : IsSimplePolygon p) (i : ℤ) :
    ∃ ℓ : E →L[ℝ] ℝ,
      0 < ℓ (p (polygonIntegerIndex N i) - p (polygonIntegerIndex N (i - 1))) ∧
      0 < ℓ (p (polygonIntegerIndex N (i + 1)) - p (polygonIntegerIndex N i)) := by
  obtain ⟨ℓ, hl, hr⟩ := hp.exists_positive_corner_functional (polygonIntegerIndex N i)
  have hprev : polygonIntegerIndex N (i - 1) =
      (finRotate N).symm (polygonIntegerIndex N i) := by
    apply (finRotate N).injective
    rw [← polygonIntegerIndex_succ, sub_add_cancel, Equiv.apply_symm_apply]
  exact ⟨ℓ, by simpa only [hprev] using hl,
    by simpa only [polygonIntegerIndex_succ] using hr⟩

theorem exists_positive_deletion_derivatives_on_finite_window
    [FiniteDimensional ℝ E] {n : ℕ} {p : Polygon E (n + 4)} (hp : IsSimplePolygon p)
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1)
    (i : ℤ) (hi : 0 ≤ i) (hin : i < n + 4) :
    ∃ ℓ : E →L[ℝ] ℝ, ∀ t : ℝ, |t - (i : ℝ)| < 3 / 4 →
      0 < ℓ (deriv (roundedPolygonParameter ρ p) t) ∧
      0 < ℓ (deriv (fun s => roundedPolygonParameter ρ
        (polygonDeleteVertex p (Fin.last (n + 3))) (deletionClock ρ (n + 4) s)) t) := by
  have hhalf : δ < 1 / 2 := by linarith
  have hdiff := hρ.differentiable (by simp)
  have hclock := contDiff_deletionClock (n + 4) hδ hhalf htail hbound hρ
  have hclockpos (t : ℝ) : 0 < deriv (deletionClock ρ (n + 4)) t := by
    linarith [(deriv_deletionClock_mem_Icc (N := n + 4) (by omega)
      hδ hhalf htail hbound hdiff hder t).1]
  obtain ⟨ℓ, hu, hv⟩ := hp.exists_positive_integer_corner_functional i
  have hαpos (t : ℝ) (ht : |t - (i : ℝ)| < 3 / 4) :
      0 < ℓ (deriv (roundedPolygonParameter ρ p) t) := by
    have ht' : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
      constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
    rw [roundedPolygonParameter, deriv_roundedVertexPath_eq_local _ hδ hhalf htail hbound hdiff i ht']
    exact (strictMono_roundedCorner_projection _ _ _ hdiff hder ℓ hu hv).1 (t - i)
  refine ⟨ℓ, fun t ht => ⟨hαpos t ht, ?_⟩⟩
  have hwindow : ∀ᶠ s : ℝ in 𝓝 t, |s - (i : ℝ)| < 3 / 4 :=
    (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const).mem_nhds ht
  by_cases hi0 : i = 0
  · subst i
    simp only [polygonIntegerIndex_zero, zero_sub, zero_add, polygonIntegerIndex_neg_one,
      polygonIntegerIndex_one (show 1 < n + 4 by omega)] at hu hv
    have heq : (fun s => roundedPolygonParameter ρ
        (polygonDeleteVertex p (Fin.last (n + 3))) (deletionClock ρ (n + 4) s)) =ᶠ[𝓝 t]
        fun s => roundedCorner ρ (p 0) ((2 : ℝ) • (p 0 - p (Fin.last (n + 3))))
          (p ⟨1, by omega⟩ - p 0) (deletionClock ρ (n + 4) s) := by
      filter_upwards [hwindow] with s hs
      exact roundedPolygon_delete_last_eq_at_zero p hmid hδ hδsmall htail hbound (by simpa using hs)
    rw [heq.deriv_eq]
    exact roundedCorner_comp_projection_deriv_pos _ _ _ hdiff hder ℓ
      (by simpa only [map_smul, smul_eq_mul] using mul_pos (by norm_num : (0 : ℝ) < 2) hu)
      hv (hclock.differentiable (by simp) t) (hclockpos t)
  · by_cases hilast : i = n + 3
    · have heq : (fun s => roundedPolygonParameter ρ
          (polygonDeleteVertex p (Fin.last (n + 3))) (deletionClock ρ (n + 4) s)) =ᶠ[𝓝 t]
          roundedPolygonParameter ρ p := by
        filter_upwards [hwindow] with s hs
        apply roundedPolygon_delete_last_eq_at_last p hmid hδ hδsmall htail hbound
        simpa only [hilast, Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using hs
      rw [heq.deriv_eq]
      exact hαpos t ht
    · by_cases hipen : i = n + 2
      · subst i
        have hidx : polygonIntegerIndex (n + 4) ((n : ℤ) + 2) = (Fin.last (n + 2)).castSucc := by
          simpa only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_ofNat] using
            polygonIntegerIndex_nat (Fin.last (n + 2)).castSucc
        have hprev : polygonIntegerIndex (n + 4) ((n : ℤ) + 2 - 1) =
            (Fin.last (n + 1)).castSucc.castSucc := by
          rw [show (n : ℤ) + 2 - 1 = n + 1 by omega]
          simpa only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] using
            polygonIntegerIndex_nat (Fin.last (n + 1)).castSucc.castSucc
        have hnext : polygonIntegerIndex (n + 4) ((n : ℤ) + 2 + 1) = Fin.last (n + 3) := by
          rw [show (n : ℤ) + 2 + 1 = n + 3 by omega]
          simpa only [Fin.val_last, Nat.cast_add, Nat.cast_ofNat] using
            polygonIntegerIndex_nat (Fin.last (n + 3))
        rw [hidx, hprev] at hu
        rw [hidx, hnext] at hv
        have heq : (fun s => roundedPolygonParameter ρ
            (polygonDeleteVertex p (Fin.last (n + 3))) (deletionClock ρ (n + 4) s)) =ᶠ[𝓝 t]
            fun s => roundedCorner ρ (p (Fin.last (n + 2)).castSucc)
              (p (Fin.last (n + 2)).castSucc - p (Fin.last (n + 1)).castSucc.castSucc)
              ((2 : ℝ) • (p (Fin.last (n + 3)) - p (Fin.last (n + 2)).castSucc))
              (deletionClock ρ (n + 4) s - ((n : ℝ) + 2)) := by
          filter_upwards [hwindow] with s hs
          apply roundedPolygon_delete_last_eq_at_penultimate p hmid hδ hδsmall htail hbound
          simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using hs
        rw [heq.deriv_eq]
        apply roundedCorner_comp_projection_deriv_pos _ _ _ hdiff hder ℓ hu
          (by simpa only [map_smul, smul_eq_mul] using mul_pos (by norm_num : (0 : ℝ) < 2) hv)
          ((hclock.differentiable (by simp) t).sub_const _)
        simpa only [deriv_sub_const] using hclockpos t
      · have heq : (fun s => roundedPolygonParameter ρ
            (polygonDeleteVertex p (Fin.last (n + 3))) (deletionClock ρ (n + 4) s)) =ᶠ[𝓝 t]
            roundedPolygonParameter ρ p := by
          filter_upwards [hwindow] with s hs
          apply roundedPolygon_delete_last_eq_of_interior p hδ hhalf htail hbound
            (show 1 ≤ i by omega) (show i < n + 2 by omega)
          constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
        rw [heq.deriv_eq]
        exact hαpos t ht

end Poincare.Manifold.Schoenflies.Plane
