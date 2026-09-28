import PoincareConjecture.Proofs.M09.MaximalRegularizedCurve
import PoincareConjecture.Proofs.M09.LocalRegularizedFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def normalizedSquareFamily {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (p : M) (Z : TangentSpace (𝓡 n) p) : ℝ → M :=
  maximalRegularizedCurve F T b 0 ⟨p, (2 : ℝ) • Z⟩

theorem normalizedSquareFamily_initial_phase {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (Z : TangentSpace (𝓡 n) p) :
    curvePhase (n := n) (normalizedSquareFamily F T b p Z) 0 =
      (⟨p, (2 : ℝ) • Z⟩ : TangentBundle (𝓡 n) M) :=
  (maximalRegularizedSolution F hM04 T b hb hwindow 0
    ⟨neg_lt_zero.mpr (Real.sqrt_pos.mpr hb), Real.sqrt_pos.mpr hb⟩ ⟨p, (2 : ℝ) • Z⟩).initial_phase

theorem normalizedSquareFamily_zero {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (Z : TangentSpace (𝓡 n) p) : normalizedSquareFamily F T b p Z 0 = p :=
  congrArg Bundle.TotalSpace.proj (normalizedSquareFamily_initial_phase F hM04 T b hb hwindow p Z)

set_option backward.isDefEq.respectTransparency false in
theorem exists_normalizedSquareFamily_smooth_zero {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (Z0 : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∃ (W : Set (TangentSpace (𝓡 n) p)) (d : ℝ), IsOpen W ∧ Z0 ∈ W ∧
      0 < d ∧ d < Real.sqrt b ∧
      ContMDiffOn (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ)) (𝓡 n) ∞
        (fun z ↦ normalizedSquareFamily F T b p z.1 z.2) (W ×ˢ Set.Ioo (-d) d) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  obtain ⟨A⟩ := nonempty_localRegularizedInitialFamily F hM04 T b hb hwindow p Z0
  let I := Set.Ioo (-A.radius) A.radius
  let d := min A.radius (Real.sqrt b / 2)
  let K := Set.Ioo (-d) d
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hd : 0 < d := lt_min A.radius_pos (by positivity)
  have hdr : d ≤ A.radius := min_le_left _ _
  have hdb : d < Real.sqrt b := (min_le_right _ _).trans_lt (by linarith)
  have hKI : K ⊆ I := by intro s hs; constructor <;> linarith [hs.1, hs.2]
  have htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have h0 : (0 : ℝ) ∈ K := ⟨neg_lt_zero.mpr hd, hd⟩
  have hsmooth (Z : TangentSpace (𝓡 n) p) (hZ : Z ∈ A.neighborhood) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.curve Z) I :=
    A.curve_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun s hs ↦ ⟨hZ, hs⟩)
  have hphase (Z : TangentSpace (𝓡 n) p) (hZ : Z ∈ A.neighborhood) :
      curvePhase (n := n) (A.curve Z) 0 =
        (⟨p, (2 : ℝ) • Z⟩ : TangentBundle (𝓡 n) M) := by
    have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
        (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
      cases h
      rfl
    have hv := A.initial_derivative Z hZ
    rw [hcast _ _ (A.curve_start Z hZ) (curveVelocity (n := n) (A.curve Z) 0)] at hv
    exact Bundle.TotalSpace.ext (A.curve_start Z hZ) (heq_of_eq hv)
  have heq (Z : TangentSpace (𝓡 n) p) (hZ : Z ∈ A.neighborhood) :
      Set.EqOn (normalizedSquareFamily F T b p Z) (A.curve Z) K := by
    let S : RegularizedIntervalSolution F T b 0 ⟨p, (2 : ℝ) • Z⟩ := {
      domain := K
      open_domain := isOpen_Ioo
      preconnected_domain := isPreconnected_Ioo
      initial_mem := h0
      time_mem := htime
      curve := A.curve Z
      isLocal := {
        smooth := (hsmooth Z hZ).mono hKI
        equation := fun s hs ↦ (regularizedEquation_iff_local F hM04 T b hb hwindow
          (A.curve Z) I I isOpen_Ioo (Set.Subset.refl _) isOpen_Ioo.uniqueDiffOn
          (hsmooth Z hZ) (A.velocity_extension Z hZ) s (hKI hs) (htime hs)).mp
            (A.equation Z hZ s (hKI hs))
      }
      initial_phase := hphase Z hZ
    }
    exact maximalRegularizedCurve_eqOn F hM04 T b hb hwindow 0 ⟨p, (2 : ℝ) • Z⟩ S
  have hfamily : ContMDiffOn (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.curve z.1 z.2) (A.neighborhood ×ˢ I) := by
    convert! A.curve_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  refine ⟨A.neighborhood, d, A.neighborhood_open, A.center_mem, hd, hdb, ?_⟩
  apply (hfamily.mono (Set.prod_mono (Set.Subset.refl _) hKI)).congr
  intro z hz
  exact heq z.1 hz.1 hz.2

end PoincareConjecture.Proofs.M09
