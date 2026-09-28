import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T2Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

theorem ball_subset_image_ball_of_inverse_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) (p : M) {R r C : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hCr : C * r < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hsource : closure (g.ball p R) ⊆ e.source)
    (hinv : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) 1 e.symm y)
    (hbound : ∀ y ∈ e '' closure (g.ball p R), ∀ v : TangentSpace (𝓡 n) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) ≤
        C * h.tangentNorm y v) :
    h.ball (e p) r ⊆ e '' g.ball p (C * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hp : p ∈ g.ball p R := by
    change g.edist p p < ENNReal.ofReal R
    simpa [edist, Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hR
  have hps : p ∈ e.source := hsource (subset_closure hp)
  let V := g.ball p R
  let W := e '' V
  have hVo : IsOpen V := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hWo : IsOpen W := e.isOpen_image_of_subset_source hVo
    (subset_closure.trans hsource)
  have hclosed : IsClosed (e '' closure V) :=
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed
  have hclosure : closure W ⊆ e '' closure V :=
    closure_minimal (image_mono subset_closure) hclosed
  have himage : e '' closure V ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsource hx)
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
  have hlength {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
      (hmap : MapsTo γ (Icc 0 c) (e '' closure V)) :
      g.edist p (e.symm (γ c)) ≤ ENNReal.ofReal C * h.pathELength γ 0 1 := by
    have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (e.symm ∘ γ) (Icc 0 c) := by
      intro u hu
      exact ((hinv (γ u) (himage (hmap hu))).comp u
        hγ.contMDiffAt).contMDiffWithinAt
    have hdist : g.edist p (e.symm (γ c)) ≤ g.pathELength (e.symm ∘ γ) 0 c :=
      Manifold.riemannianEDist_le_pathELength hreg
        (by simpa only [Function.comp_apply, hγ0] using e.left_inv hps) rfl hc.1
    apply hdist.trans
    apply (h.pathELength_comp_le_of_tangentNorm_le_on_Icc g hC.le hγ
      (fun u hu => hinv (γ u) (himage (hmap hu)))
      (fun u hu => hbound (γ u) (hmap hu))).trans
    exact mul_le_mul' le_rfl (show h.pathELength γ 0 c ≤ h.pathELength γ 0 1 from
      Manifold.pathELength_mono le_rfl hc.2)
  have hshort : ENNReal.ofReal C * h.pathELength γ 0 1 < ENNReal.ofReal (C * r) := by
    rw [ENNReal.ofReal_mul hC.le]
    exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top hlen
  have hstays : MapsTo γ (Icc (0 : ℝ) 1) W := by
    by_contra hnot
    have hend : γ 1 ∉ W ∨ ∃ c ∈ Icc (0 : ℝ) 1, γ c ∉ W := by
      right
      simpa only [MapsTo, not_forall, exists_prop] using hnot
    obtain ⟨b, hb, hγb⟩ : ∃ b ∈ Icc (0 : ℝ) 1, γ b ∉ W := by
      rcases hend with h | h
      · exact ⟨1, by norm_num, h⟩
      · exact h
    have hbpos : 0 < b := lt_of_le_of_ne hb.1 (by
      intro heq
      subst b
      exact hγb (by rw [hγ0]; exact mem_image_of_mem e hp))
    let η : ℝ → N := fun u => γ (b * u)
    obtain ⟨c, hc, hfront, hmap⟩ := PoincareConjecture.exists_first_exit_of_continuous
      (γ := η) (hγ.continuous.comp (continuous_const.mul continuous_id)) hWo
      (by change γ (b * 0) ∈ e '' g.ball p R
          simpa only [mul_zero, hγ0] using mem_image_of_mem e hp)
      (by simpa [η] using hγb)
    have hbc : b * c ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hb.1 hc.1.le, (mul_le_of_le_one_right hb.1 hc.2).trans hb.2⟩
    have hmap' : MapsTo γ (Icc 0 (b * c)) (e '' closure V) := by
      intro u hu
      have huc : u / b ∈ Icc (0 : ℝ) c :=
        ⟨div_nonneg hu.1 hb.1, (div_le_iff₀ hbpos).mpr (by simpa [mul_comm] using hu.2)⟩
      have hh := hclosure (hmap huc)
      simpa [η, mul_div_cancel₀ _ hbpos.ne'] using hh
    have hinside : e.symm (γ (b * c)) ∈ V :=
      (hlength hbc hmap').trans_lt (hshort.trans_le (ENNReal.ofReal_le_ofReal hCr.le))
    have hw : η c ∈ W := by
      exact ⟨e.symm (γ (b * c)), hinside,
        e.right_inv (himage (hmap' ⟨hbc.1, le_rfl⟩))⟩
    rw [frontier, hWo.interior_eq] at hfront
    exact hfront.2 hw
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) (e '' closure V) :=
    fun u hu => image_mono subset_closure (hstays hu)
  refine ⟨e.symm y, ?_, e.right_inv (himage (by
    simpa only [hγ1] using hmap (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)))⟩
  have hd := (hlength (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hmap).trans_lt hshort
  change g.edist p (e.symm y) < ENNReal.ofReal (C * r)
  simpa only [hγ1] using hd

omit [T3Space M] [T2Space N] in

theorem image_ball_subset_ball_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) (p : M) {r C : ℝ}
    (hC : 0 < C) (hsource : g.ball p r ⊆ e.source)
    (he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) 1 e x)
    (hbound : ∀ x ∈ g.ball p r, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v) :
    e '' g.ball p r ⊆ h.ball (e p) (C * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hx zero_lt_one
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) (g.ball p r) := by
    intro u hu
    exact ((Manifold.riemannianEDist_le_pathELength
      (hγ.contMDiffOn.mono (Icc_subset_Icc_right hu.2)) hγ0 rfl hu.1).trans
        (Manifold.pathELength_mono le_rfl hu.2)).trans_lt hlen
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (e ∘ γ) (Icc 0 1) := by
    intro u hu
    exact ((he (γ u) (hsource (hmap hu))).comp u hγ.contMDiffAt).contMDiffWithinAt
  have hd : h.edist (e p) (e x) ≤ h.pathELength (e ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hreg
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  apply (hd.trans (g.pathELength_comp_le_of_tangentNorm_le_on_Icc h hC.le hγ
    (fun u hu => he (γ u) (hsource (hmap hu)))
    (fun u hu => hbound (γ u) (hmap hu)))).trans_lt
  rw [ENNReal.ofReal_mul hC.le]
  exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top hlen

end PoincareConjecture.RiemannianMetric
