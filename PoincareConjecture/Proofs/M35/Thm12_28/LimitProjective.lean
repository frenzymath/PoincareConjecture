import PoincareConjecture.Proofs.M35.Thm12_28.BlowupSequence
import PoincareConjecture.Proofs.M35.Thm12_28.EvenImmersion
import PoincareConjecture.Proofs.M35.Thm12_28.PolarCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderImmersion

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem cylinder_excludes_antipodal_product {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ I)
    (c : StandardCylinderSpace → C.carrier)
    (hc : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c)
    (heven : ∀ p : StandardCylinderSpace, c (-p.1, p.2) = c p)
    (hcentral : ∀ q : UnitTwoSphere, c (q, 0) ∈ U) : False := by
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq StandardCapSpace (by norm_num : (0 : ℝ) ≤ 1)
  let q₀ : UnitTwoSphere :=
    ⟨v₀, by simpa only [Metric.mem_sphere, dist_zero_right] using hv₀⟩
  have htime : a + s / Q ∈ J := (e.forward s hs (c (q₀, 0))).property
  let d := sliceDiffeomorph htime
  let f₀ : C.carrier → StandardCapSpace := d ∘ e.forward s hs
  have hf₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f₀ U :=
    d.contMDiff.comp_contMDiffOn (e.forward_smooth s hs)
  have hinj₀ (z : C.carrier) (hz : z ∈ U) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f₀ z) := by
    have hreg := (e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hz)
    have hf := hreg.mdifferentiableAt (by simp)
    rw [mfderiv_comp z (d.contMDiff.mdifferentiable (by simp) _) hf]
    exact (d.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (e.mfderiv_injective hU s hs hz)
  let f : StandardCapSpace → StandardCapSpace := (f₀ ∘ c) ∘ spherePolarMap q₀
  have hvalid (x : StandardCapSpace) (hx : x ∈ Metric.sphere (0 : StandardCapSpace) 1) :
      c (spherePolarMap q₀ x) ∈ U := by
    rw [spherePolarMap_sphere q₀ (⟨x, hx⟩ : UnitTwoSphere)]
    exact hcentral ⟨x, hx⟩
  have hsmooth (x : StandardCapSpace) (hx : x ∈ Metric.sphere (0 : StandardCapSpace) 1) :
      ContDiffAt ℝ 1 f x := by
    have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
    have ho := hf₀.contMDiffAt (hU.mem_nhds (hvalid x hx))
    have hcomp := (ho.comp (spherePolarMap q₀ x) (hc.contMDiff _)).comp x
      (spherePolarMap_contMDiffAt q₀ hx0)
    exact contMDiffAt_iff_contDiffAt.mp (hcomp.of_le (by simp))
  have hfeven (x : StandardCapSpace) : f (-x) = f x := by
    by_cases hx : x = 0
    · simp only [hx, neg_zero]
    · change f₀ (c (spherePolarMap q₀ (-x))) = f₀ (c (spherePolarMap q₀ x))
      rw [spherePolarMap_neg q₀ hx, heven]
  obtain ⟨x, hx, hsingular⟩ := exists_singular_derivative_of_even f hsmooth hfeven
  apply hsingular
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  have ho := (hf₀.contMDiffAt (hU.mem_nhds (hvalid x hx))).mdifferentiableAt (by simp)
  have hp := (spherePolarMap_contMDiffAt q₀ hx0).mdifferentiableAt (by simp)
  have hc' := hc.mdifferentiable (by simp) (spherePolarMap q₀ x)
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp x (ho.comp _ hc') hp,
    mfderiv_comp (spherePolarMap q₀ x) ho hc']
  exact ((hinj₀ _ (hvalid x hx)).comp
    ((hc (spherePolarMap q₀ x)).mfderivToContinuousLinearEquiv (by simp)).injective).comp
      (spherePolarMap_mfderiv_injective q₀ hx0)

theorem blowupSequence_limit_no_antipodal_product (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    {J : Set ℝ} (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR) J)
    (c : StandardCylinderSpace → L.limit.sliceCarrier.carrier)
    (hc : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c)
    (heven : ∀ p : StandardCylinderSpace, c (-p.1, p.2) = c p) : False := by
  have hcompact : IsCompact (range (fun q : UnitTwoSphere => c (q, 0))) :=
    isCompact_range (hc.contMDiff.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨k, hk⟩ := hcompact.elim_directed_cover L.exhaustion.space
    L.exhaustion.space_open (by rw [L.exhaustion.space_covers]; exact subset_univ _)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  exact cylinder_excludes_antipodal_product E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
    c hc heven (fun q => hk (mem_range_self q))

end PoincareConjecture.M35.OrdinaryRealization
