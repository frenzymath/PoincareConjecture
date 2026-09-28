import PoincareConjecture.Proofs.M09.GeometricODE
import PoincareConjecture.Proofs.M09.VelocityRestriction









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

def LocalRegularizedEquation {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (s : ℝ) : Prop :=
  ∃ p : M, γ s ∈ (chartAt V p).source ∧
    let a : ℝ → V := fun t ↦ (chartAt V p) (γ t)
    HasDerivAt (fun t ↦ (a t, deriv a t))
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a s, deriv a s))) s

theorem regularizedEquation_restrict_iff {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (I K : Set ℝ) (hKI : K ⊆ I)
    (hI : UniqueDiffOn ℝ I) (hK : UniqueDiffOn ℝ K)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ K) :
    regularizedLGeodesicEquation F T γ K
      (restrictVelocityExtension γ I K hKI hI hK hγ E) s ↔
      regularizedLGeodesicEquation F T γ I E s := by
  unfold regularizedLGeodesicEquation regularizedEulerResidual
  rw [restrictVelocityExtension_pullback F (fun r ↦ T - r ^ 2) γ I K hKI hI hK hγ E s hs,
    curveVelocityWithin_eq_curveVelocity γ K s (hK s hs) (hγ s (hKI hs)),
    curveVelocityWithin_eq_curveVelocity γ I s (hI s (hKI hs)) (hγ s (hKI hs))]

theorem regularizedEquation_iff_chart_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) (γ : ℝ → M)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) (hK : UniqueDiffOn ℝ K)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (E : ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K))
    (s : ℝ) (hs : s ∈ K) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hp : γ s ∈ (chartAt V p).source) :
    regularizedLGeodesicEquation F T γ K E s ↔
      let a : ℝ → V := fun t ↦ (chartAt V p) (γ t)
      HasDerivAt (fun t ↦ (a t, deriv a t))
        (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
          (s, (a s, deriv a s))) s := by
  let W : Set ℝ := U ∩ γ ⁻¹' (chartAt V p).source
  have hW : IsOpen W :=
    hγ.continuousOn.isOpen_inter_preimage hU (chartAt V p).open_source
  have hsW : s ∈ W := ⟨hKU hs, hp⟩
  let L := K ∩ W
  have hL : UniqueDiffOn ℝ L := hK.inter hW
  have hsL : s ∈ L := ⟨hs, hsW⟩
  have hgd : ∀ t ∈ K, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t :=
    fun t ht ↦ (hγ.contMDiffAt (hU.mem_nhds (hKU ht))).mdifferentiableAt (by simp)
  let E' := restrictVelocityExtension γ K L Set.inter_subset_left hK hL hgd E
  let a : ℝ → V := fun t ↦ (chartAt V p) (γ t)
  have ha : ContDiffOn ℝ ∞ a W :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun _ ht ↦ ht.2)).contDiffOn
  have hv : ContDiffOn ℝ ∞ (deriv a) W := ha.deriv_of_isOpen hW (by simp)
  have had : ∀ t ∈ L, HasDerivAt a (deriv a t) t :=
    fun t ht ↦ ((ha.contDiffAt (hW.mem_nhds ht.2)).differentiableAt (by simp)).hasDerivAt
  have hvd : HasDerivAt (deriv a) (deriv (deriv a) s) s :=
    ((hv.contDiffAt (hW.mem_nhds hsW)).differentiableAt (by simp)).hasDerivAt
  have hequiv := regularizedEquation_iff_coordinate_acceleration F hM04 T b hb hwindow
    p γ (deriv a) W L hW Set.inter_subset_right hL hv (fun t ht ↦ hgd t ht.1)
    had (fun _ ht ↦ ht.2.2) E' s hsL htime (deriv (deriv a) s) hvd
  rw [← regularizedEquation_restrict_iff F T γ K L Set.inter_subset_left hK hL hgd E s hsL]
  constructor
  · intro heq
    exact (had s hsL).prodMk (hvd.congr_deriv (hequiv.mp heq))
  · intro hd
    apply hequiv.mpr
    exact hvd.unique hd.snd

theorem regularizedEquation_iff_local {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ : ℝ → M)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) (hK : UniqueDiffOn ℝ K)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (E : ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K))
    (s : ℝ) (hs : s ∈ K) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    regularizedLGeodesicEquation F T γ K E s ↔ LocalRegularizedEquation F T γ s := by
  constructor
  · intro heq
    exact ⟨γ s, mem_chart_source V (γ s),
      (regularizedEquation_iff_chart_hasDerivAt F hM04 T b hb hwindow (γ s) γ
        U K hU hKU hK hγ E s hs htime (mem_chart_source V (γ s))).mp heq⟩
  · rintro ⟨p, hp, hd⟩
    exact (regularizedEquation_iff_chart_hasDerivAt F hM04 T b hb hwindow p γ
      U K hU hKU hK hγ E s hs htime hp).mpr hd

theorem LocalRegularizedEquation.congr {J : Set ℝ} {F : RicciFlow n M J}
    {T s : ℝ} {γ δ : ℝ → M} (h : LocalRegularizedEquation F T γ s)
    (heq : γ =ᶠ[𝓝 s] δ) : LocalRegularizedEquation F T δ s := by
  obtain ⟨p, hp, hd⟩ := h
  have ha : (fun t ↦ (chartAt V p) (γ t)) =ᶠ[𝓝 s]
      (fun t ↦ (chartAt V p) (δ t)) := heq.fun_comp (chartAt V p)
  have hphase := ha.prodMk ha.deriv
  refine ⟨p, ?_, ?_⟩
  · rwa [← heq.eq_of_nhds]
  · have hd' := hd.congr_of_eventuallyEq hphase.symm
    simpa only [ha.eq_of_nhds, ha.deriv_eq] using hd'

end PoincareConjecture.Proofs.M09
