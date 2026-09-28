import PoincareConjecture.Proofs.M09.LocalSmoothInverse
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {X : Type*} [TopologicalSpace X]

theorem exists_curve_time_chart (γ : ℝ → X) (hγ : Continuous γ)
    (e : OpenPartialHomeomorph X ℝ) (t : ℝ) (ht : γ t ∈ e.source)
    (hcoord : ContDiffOn ℝ ∞ (fun s => e (γ s)) (γ ⁻¹' e.source))
    (hder : deriv (fun s => e (γ s)) t ≠ 0) :
    ∃ k : OpenPartialHomeomorph ℝ X, t ∈ k.source ∧
      ∀ s ∈ k.source, k s = γ s := by
  have hinj : Injective (fderiv ℝ (fun s => e (γ s)) t) := by
    intro a b h
    simp only [fderiv_eq_deriv_mul] at h
    exact mul_left_cancel₀ hder h
  have hbij : Bijective (fderiv ℝ (fun s => e (γ s)) t) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  obtain ⟨e0, ht0, h0U, he0, _, _⟩ :=
    PoincareConjecture.Proofs.M09.exists_smooth_local_inverse (fun s => e (γ s))
      (γ ⁻¹' e.source) (e.open_source.preimage hγ) hcoord t ht hbij
  refine ⟨e0.trans e.symm, ⟨ht0, ?_⟩, ?_⟩
  · change e0 t ∈ e.target
    rw [congrFun he0 t]
    exact e.map_source ht
  · intro s hs
    change e.symm (e0 s) = γ s
    rw [congrFun he0 s]
    exact e.left_inv (h0U hs.1)

theorem curve_isOpenMap_of_time_charts (γ : ℝ → X)
    (hchart : ∀ t, ∃ k : OpenPartialHomeomorph ℝ X, t ∈ k.source ∧
      ∀ s ∈ k.source, k s = γ s) : IsOpenMap γ := by
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨t, ht, rfl⟩
  obtain ⟨k, htk, hk⟩ := hchart t
  refine ⟨k '' (k.source ∩ U), ?_, k.isOpen_image_source_inter hU, ⟨t, ⟨htk, ht⟩, hk t htk⟩⟩
  rintro z ⟨s, hs, rfl⟩
  exact ⟨s, hs.2, (hk s hs.1).symm⟩

theorem curve_injOn_interval_of_time_chart (γ : ℝ → X)
    (k : OpenPartialHomeomorph ℝ X) (h0 : 0 ∈ k.source)
    (hk : ∀ s ∈ k.source, k s = γ s) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn γ (Ioo (-ε) ε) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (k.open_source.mem_nhds h0)
  have hI : Ioo (-ε) ε ⊆ k.source := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hball
  refine ⟨ε, hε, ?_⟩
  intro s hs t ht hst
  apply k.injOn (hI hs) (hI ht)
  rw [hk s (hI hs), hk t (hI ht)]
  exact hst

end PoincareConjecture.M25.Topology3D
