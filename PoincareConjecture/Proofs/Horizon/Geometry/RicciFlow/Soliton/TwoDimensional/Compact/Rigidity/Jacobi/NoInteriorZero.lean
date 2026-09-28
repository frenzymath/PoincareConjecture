import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Jacobi.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.NoConjugate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

open ConnectionAlongCurve ConnectionVariation ConjugateFrame

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

private theorem exists_normal_ne_zero (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin 2), u ≠ 0 ∧ inner ℝ v u = 0 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  have hdim := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 1) hv
  obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
    (M := (Submodule.span ℝ {v})ᗮ)).mp (by rw [hdim]; norm_num)
  refine ⟨u, ?_, ?_⟩
  · intro h
    apply hu
    exact Subtype.ext h
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.property



theorem scalar_jacobi_ne_zero_of_minimizing (D : LeviCivitaData g)
    {γ : ℝ → M} {ε C c : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hgeo : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hspeed : ∀ t ∈ Ioo (-ε) (1 + ε),
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = C)
    (hmin : g.edist (γ 0) (γ 1) = ENNReal.ofReal C)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Ioo (-ε) (1 + ε)))
    (hode : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv φ) t = -(D.scalarCurvature (γ t) * C ^ 2 / 2) * φ t)
    (hzero : φ 0 = 0) (hdzero : deriv φ 0 ≠ 0) (hc : c ∈ Ioo (0 : ℝ) 1) :
    φ c ≠ 0 := by
  let a := -ε / 2
  let b := 1 + ε / 2
  have ha : a < 0 := by dsimp [a]; linarith
  have hb : 1 < b := by dsimp [b]; linarith
  have hab : a < b := by linarith
  have hsub : Icc a b ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h01' := h01.trans Ioo_subset_Icc_self
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ (Ioo (-ε) (1 + ε)) :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
  have hγt (t : ℝ) (ht : t ∈ Icc a b) :=
    hγ.contMDiffAt (isOpen_Ioo.mem_nhds (hsub ht))
  obtain ⟨P, hi, hP, hp⟩ := exists_orthonormal_parallel_transport g hab
    isOpen_Ioo hγ hsub
  let v := (P a).inverse (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ a 1)
  have ha' : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hPv : P a v = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ a 1 :=
    (hi a ha').self_apply_inverse _
  have hv : v ≠ 0 := by
    intro hz
    have hT : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ a 1 = 0 := by simpa [hz] using hPv.symm
    have hs := hspeed a (hsub ha')
    rw [hT] at hs
    simp [RiemannianMetric.tangentNorm] at hs
    linarith
  obtain ⟨u, hu, huv⟩ := exists_normal_ne_zero v hv
  have hPv' (t : ℝ) (ht : t ∈ Icc a b) :
      P t v = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 :=
    g.parallel_frame_velocity hab isOpen_Ioo hgeo hγ hsub hi hP v hPv ht
  have horth (t : ℝ) (ht : t ∈ Icc a b) :
      g.inner (γ t) (P t u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = 0 := by
    rw [← hPv' t ht, hp t ht, real_inner_comm]
    exact huv
  let J := fun t => P t (φ t • u)
  have hφ' : ContDiffOn ℝ ∞ φ (Ioo a b) :=
    hφ.mono (Ioo_subset_Icc_self.trans hsub)
  have hJs (t : ℝ) (ht : t ∈ Ioo a b) :
      ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
    exact contDiffAt_frame_field (fun w => (hP t (Ioo_subset_Icc_self ht) w).1)
      ((hφ'.contDiffAt (isOpen_Ioo.mem_nhds ht)).smul contDiffAt_const)
  have hjac (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) := by
    apply D.jacobi_of_scalar_in_parallel_frame (h01 ht) hi
      (fun s hs => hγt s (Ioo_subset_Icc_self hs)) hP hφ' u (horth t (h01' ht))
    have hnorm : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = C ^ 2 := by
      have hs := congrArg (fun r : ℝ => r ^ 2) (hspeed t (hsub (h01' ht)))
      rw [RiemannianMetric.tangentNorm, Real.sq_sqrt] at hs
      · exact hs
      · by_cases hz : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 = 0
        · simp [hz]
        · exact (g.pos _ _ hz).le
    rw [hnorm, hode t ht]
    ring
  have hJ0 : J 0 = 0 := by simp [J, hzero]
  have hdJ0 : manifoldCovDerivAlong g γ J 1 0 ≠ 0 := by
    change manifoldCovDerivAlong g γ (fun t => P t (φ t • u)) 1 0 ≠ 0
    rw [covDeriv_frame_field (W := fun t => φ t • u)
      (h01 (by simp)) hi (hγt 0 (h01' (by simp)))
      (hP 0 (h01' (by simp)))
      ((hφ'.contDiffAt (isOpen_Ioo.mem_nhds (h01 (by simp)))).smul contDiffAt_const)]
    have hd : deriv (fun t => φ t • u) 0 = deriv φ 0 • u := by
      exact ((hφ'.contDiffAt (isOpen_Ioo.mem_nhds (h01 (by simp)))).differentiableAt
        (by simp)).hasDerivAt.smul_const u |>.deriv
    rw [hd]
    exact fun h => (smul_ne_zero hdzero hu) ((hi 0 (h01' (by simp))).injective (by simpa using h))
  have hsm : Icc (a / 2) ((1 + b) / 2) ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hnonzero := Conjugate.jacobi_ne_zero_of_minimizing g D
    (a := a / 2) (b := (1 + b) / 2) (by linarith) (by linarith) hc isOpen_Ioo
    (hγ.mono (Ioo_subset_Icc_self.trans hsub))
    (fun t ht => hgeo t (hsub (Ioo_subset_Icc_self ht))) hsm hJs hjac hJ0 hdJ0 hC
    (fun t ht => hspeed t (hsub (h01' ht))) hmin
  intro hz
  apply hnonzero
  simp [J, hz]

end PoincareConjecture.LeviCivitaData
