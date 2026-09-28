import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Maximum
import Mathlib.Analysis.Calculus.LocalExtr.Basic











noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



def HeatLowerContacts {g : ℝ → RiemannianMetric n M}
    (D : ∀ t, LeviCivitaData (g t)) (U : Set M)
    (J : Set ℝ) (v : M → ℝ → ℝ) : Prop :=
  ∀ x ∈ U, ∀ t ∈ J, ∀ (ψ : M → ℝ) (W : Set M),
    IsOpen W → x ∈ W → ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ W →
    ψ x = v x t → (∀ᶠ y in 𝓝 x, ψ y ≤ v y t) →
    ∃ (τ : ℝ → ℝ) (d : ℝ), HasDerivAt τ d t ∧ τ t = v x t ∧
      (∀ᶠ s in 𝓝 t, v x s ≤ τ s) ∧
      (D t).laplacian ψ x ≤ d

theorem comparison_on_Icc
    {D : Set M} (hD : IsCompact D) {g : ℝ → RiemannianMetric n M}
    (conn : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hab : a < b) {u v ut : M → ℝ → ℝ}
    (hu : ContinuousOn (fun z : M × ℝ => u z.1 z.2) (D ×ˢ Icc a b))
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (D ×ˢ Icc a b))
    (hus : ∀ t ∈ Ioo a b,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t) (interior D))
    (hud : ∀ x ∈ interior D, ∀ t ∈ Ioo a b, HasDerivAt (u x) (ut x t) t)
    (hup : ∀ x ∈ interior D, ∀ t ∈ Ioo a b,
      ut x t ≤ (conn t).laplacian (fun y => u y t) x)
    (hvs : HeatLowerContacts conn (interior D) (Ioo a b) v)
    (hinit : ∀ x ∈ D, u x a ≤ v x a)
    (hlateral : ∀ x ∈ D, x ∉ interior D → ∀ t ∈ Icc a b, u x t ≤ v x t) :
    ∀ x ∈ D, ∀ t ∈ Icc a b, u x t ≤ v x t := by
  have hprior : ∀ x ∈ D, ∀ t ∈ Ico a b, u x t ≤ v x t := by
    intro x hx t ht
    by_contra hnot
    have hpos : 0 < u x t - v x t := sub_pos.mpr (lt_of_not_ge hnot)
    have htpos : a < t := by
      rcases ht.1.eq_or_lt with heq | hlt
      · exact False.elim ((not_lt_of_ge (hinit x hx)) (heq ▸ lt_of_not_ge hnot))
      · exact hlt
    let ε : ℝ := (u x t - v x t) / (2 * (t - a))
    have hε : 0 < ε := div_pos hpos (mul_pos (by norm_num) (sub_pos.mpr htpos))
    let w : M × ℝ → ℝ := fun z => u z.1 z.2 - v z.1 z.2 - ε * (z.2 - a)
    have hw : ContinuousOn w (D ×ˢ Icc a t) :=
      ((hu.sub hv).mono (prod_mono_right (Icc_subset_Icc_right ht.2.le))).sub
        (by fun_prop)
    obtain ⟨z, hz, hzmax⟩ := (hD.prod isCompact_Icc).exists_isMaxOn
      (show (D ×ˢ Icc a t).Nonempty from ⟨(x, t), hx, htpos.le, le_rfl⟩) hw
    have hwxt : 0 < w (x, t) := by
      dsimp [w, ε]
      have htne : t - a ≠ 0 := (sub_pos.mpr htpos).ne'
      field_simp
      nlinarith
    have hwz : 0 < w z := hwxt.trans_le (hzmax ⟨hx, htpos.le, le_rfl⟩)
    have hzT : z.2 ∈ Icc a b := ⟨hz.2.1, hz.2.2.trans ht.2.le⟩
    have hzpos : a < z.2 := by
      by_contra hn
      have hza : z.2 = a := le_antisymm (le_of_not_gt hn) hz.2.1
      have hi := hinit z.1 hz.1
      have hp : 0 < u z.1 a - v z.1 a := by simpa [w, hza] using hwz
      linarith
    have huz : v z.1 z.2 < u z.1 z.2 := by
      have := mul_nonneg hε.le (sub_nonneg.mpr hz.2.1)
      dsimp [w] at hwz
      linarith
    have hzU : z.1 ∈ interior D := by
      by_contra hn
      exact (not_lt_of_ge (hlateral z.1 hz.1 hn z.2 hzT)) huz
    have hzI : z.2 ∈ Ioo a b := ⟨hzpos, hz.2.2.trans_lt ht.2⟩
    let C := u z.1 z.2 - v z.1 z.2
    let ψ : M → ℝ := fun y => u y z.2 - C
    have hψs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ (interior D) :=
      (hus z.2 hzI).sub contMDiffOn_const
    have hψeq : ψ z.1 = v z.1 z.2 := by dsimp [ψ, C]; ring
    have hψle : ∀ᶠ y in 𝓝 z.1, ψ y ≤ v y z.2 := by
      filter_upwards [isOpen_interior.mem_nhds hzU] with y hy
      have h := hzmax (show (y, z.2) ∈ D ×ˢ Icc a t from ⟨interior_subset hy, hz.2⟩)
      dsimp [w, ψ, C] at *
      linarith
    obtain ⟨τ, d, hτd, hτeq, hτge, hψp⟩ :=
      hvs z.1 hzU z.2 hzI ψ (interior D) isOpen_interior hzU hψs hψeq hψle
    have hψlap : (conn z.2).laplacian ψ z.1 =
        (conn z.2).laplacian (fun y => u y z.2) z.1 := by
      change (conn z.2).laplacian
        (fun y => u y z.2 - C) z.1 = _
      rw [LeviCivitaData.Dirichlet.laplacian_sub_on (conn z.2) isOpen_interior
          (hus z.2 hzI) (show ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (fun _ : M => C) (interior D) from contMDiffOn_const) hzU]
      have hconst : (conn z.2).laplacian (fun _ : M => C) z.1 = 0 := by
        simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
          LeviCivitaData.hessianOnFields, mvfderiv_const]
      rw [hconst, sub_zero]
    rw [hψlap] at hψp
    have hp := hup z.1 hzU z.2 hzI
    have hd : HasDerivAt (fun s => u z.1 s - τ s - ε * (s - a))
        (ut z.1 z.2 - d - ε) z.2 := by
      convert ((hud z.1 hzU z.2 hzI).sub hτd).sub
        (((hasDerivAt_id z.2).sub_const a).const_mul ε) using 1 <;>
        first | rfl | simp
    have htm : IsLocalMaxOn (fun s => u z.1 s - τ s - ε * (s - a))
        (Icc a t) z.2 := by
      filter_upwards [self_mem_nhdsWithin, hτge.filter_mono nhdsWithin_le_nhds]
        with s hs hτs
      have h := hzmax (show (z.1, s) ∈ D ×ˢ Icc a t from ⟨hz.1, hs⟩)
      dsimp [w] at h
      change u z.1 s - τ s - ε * (s - a) ≤
        u z.1 z.2 - τ z.2 - ε * (z.2 - a)
      rw [hτeq]
      linarith
    have hcone : a - z.2 ∈ posTangentConeAt (Icc a t) z.2 :=
      sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Icc a t).segment_subset hz.2 ⟨le_rfl, htpos.le⟩)
    have hdpos := htm.hasFDerivWithinAt_nonpos hd.hasDerivWithinAt.hasFDerivWithinAt hcone
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hdpos
    nlinarith
  intro x hx t ht
  have huc : ContinuousOn (u x) (Icc a b) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx, hs⟩)
  have hvc : ContinuousOn (v x) (Icc a b) :=
    hv.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx, hs⟩)
  have h := le_on_closure (hprior x hx)
    (show ContinuousOn (u x) (closure (Ico a b)) by simpa [closure_Ico hab.ne] using huc)
    (show ContinuousOn (v x) (closure (Ico a b)) by simpa [closure_Ico hab.ne] using hvc)
  exact h (by simpa [closure_Ico hab.ne] using ht)

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
