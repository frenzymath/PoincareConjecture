import PoincareConjecture.Proofs.M34.Standard.PathLengthComparison
import PoincareConjecture.Definitions.Ch09.NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

section ArbitraryDimensions

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]




theorem pathELength_comp_le_of_pointwise_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (f : M → N) {U : Set M} (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 m) 1 f x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 m) f x v) ≤ C * g.tangentNorm x v)
    (γ : ℝ → M) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U) :
    h.pathELength (f ∘ γ) a b ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  apply h.pathELength_le_mul_of_speed_le g (f ∘ γ) γ a b hC
  intro t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hfd := (hf (γ t) (hγU ht')).mdifferentiableAt (by simp)
  have hγd := ((hγ t ht').contMDiffAt
    (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ) (𝓡 m) (f ∘ γ) t 1 =
      mfderiv (𝓡 n) (𝓡 m) f (γ t) (mfderiv 𝓘(ℝ) (𝓡 n) γ t 1) :=
    mfderiv_comp_apply t hfd hγd 1
  change h.tangentNorm (f (γ t)) _ ≤ _
  rw [hd]
  exact hbound (γ t) (hγU ht') _




theorem admissiblePath_sInf_image_le_mul
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (f : M → N) (U : Set M) (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 m) 1 f x)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 m) f x v) ≤ C * g.tangentNorm x v)
    (x y : M) :
    sInf {L | ∃ η : ℝ → N, ContMDiffOn 𝓘(ℝ) (𝓡 m) 1 η (Icc (0 : ℝ) 1) ∧
      η 0 = f x ∧ η 1 = f y ∧ η '' Icc (0 : ℝ) 1 ⊆ f '' U ∧
        L = h.pathELength η 0 1} ≤
      ENNReal.ofReal C * sInf {L | ∃ γ : ℝ → M,
        ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc (0 : ℝ) 1) ∧
          γ 0 = x ∧ γ 1 = y ∧ γ '' Icc (0 : ℝ) 1 ⊆ U ∧
            L = g.pathELength γ 0 1} := by
  have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  apply (ENNReal.inv_mul_le_iff hc0 ENNReal.ofReal_ne_top).mp
  apply le_sInf
  rintro L ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩
  have hmaps : MapsTo γ (Icc (0 : ℝ) 1) U := fun t ht => hγU ⟨t, ht, rfl⟩
  have hη : ContMDiffOn 𝓘(ℝ) (𝓡 m) 1 (f ∘ γ) (Icc (0 : ℝ) 1) :=
    (show ContMDiffOn (𝓡 n) (𝓡 m) 1 f U from
      fun z hz => (hf z hz).contMDiffWithinAt).comp hγ hmaps
  have hηU : (f ∘ γ) '' Icc (0 : ℝ) 1 ⊆ f '' U := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨γ t, hmaps ht, rfl⟩
  have hpath := g.pathELength_comp_le_of_pointwise_tangentNorm_le h f hf hC.le hbound
    γ 0 1 hγ hmaps
  have hi : sInf {L | ∃ η : ℝ → N,
      ContMDiffOn 𝓘(ℝ) (𝓡 m) 1 η (Icc (0 : ℝ) 1) ∧
        η 0 = f x ∧ η 1 = f y ∧ η '' Icc (0 : ℝ) 1 ⊆ f '' U ∧
          L = h.pathELength η 0 1} ≤ h.pathELength (f ∘ γ) 0 1 :=
    sInf_le ⟨f ∘ γ, hη, by simp only [Function.comp_apply, hγ0],
      by simp only [Function.comp_apply, hγ1], hηU, rfl⟩
  exact (mul_le_mul_right (hi.trans hpath) (ENNReal.ofReal C)⁻¹).trans_eq
    (ENNReal.inv_mul_cancel_left hc0 ENNReal.ofReal_ne_top)

end ArbitraryDimensions

section FrozenIntrinsic

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]



theorem intrinsicEDist_image_le_mul
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : M → N) (U : Set M) (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) 1 f x)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v)
    (x y : M) :
    intrinsicEDist h (f '' U) (f x) (f y) ≤ ENNReal.ofReal C * intrinsicEDist g U x y :=
  g.admissiblePath_sInf_image_le_mul h f U hf hC hbound x y



theorem intrinsicDiameter_image_le_mul
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : M → N) (U : Set M) (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) 1 f x)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v) :
    intrinsicDiameter h (f '' U) ≤ ENNReal.ofReal C * intrinsicDiameter g U := by
  apply sSup_le
  rintro L ⟨p, rfl⟩
  obtain ⟨x, hx, hfx⟩ := p.1.property
  obtain ⟨y, hy, hfy⟩ := p.2.property
  change intrinsicEDist h (f '' U) p.1.val p.2.val ≤ _
  rw [← hfx, ← hfy]
  have hsource : intrinsicEDist g U x y ≤ intrinsicDiameter g U :=
    le_iSup_of_le (⟨x, hx⟩, ⟨y, hy⟩) le_rfl
  exact (g.intrinsicEDist_image_le_mul h f U hf hC hbound x y).trans
    (mul_le_mul_right hsource (ENNReal.ofReal C))



theorem intrinsicDiameter_image_le_mul_of_isOpen
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : M → N) {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f U) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v) :
    intrinsicDiameter h (f '' U) ≤ ENNReal.ofReal C * intrinsicDiameter g U :=
  g.intrinsicDiameter_image_le_mul h f U
    (fun x hx => (hf x hx).contMDiffAt (hU.mem_nhds hx)) hC hbound

end FrozenIntrinsic

end PoincareConjecture.RiemannianMetric
